%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:48 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   51 (  64 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 ( 122 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_39,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_73,axiom,(
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

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_14,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_39,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_22,plain,(
    ! [A_11] :
      ( v2_tex_2(u1_struct_0(A_11),A_11)
      | ~ v1_tdlat_3(A_11)
      | ~ m1_subset_1(u1_struct_0(A_11),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_43,plain,(
    ! [A_11] :
      ( v2_tex_2(u1_struct_0(A_11),A_11)
      | ~ v1_tdlat_3(A_11)
      | ~ l1_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_22])).

tff(c_28,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_18,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_61,plain,(
    ! [A_29,B_30] :
      ( r2_hidden(A_29,B_30)
      | v1_xboole_0(B_30)
      | ~ m1_subset_1(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,(
    ! [A_29,A_1] :
      ( r1_tarski(A_29,A_1)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_29,k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_69,plain,(
    ! [A_31,A_32] :
      ( r1_tarski(A_31,A_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(A_32)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_65])).

tff(c_76,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_69])).

tff(c_138,plain,(
    ! [C_52,A_53,B_54] :
      ( v2_tex_2(C_52,A_53)
      | ~ v2_tex_2(B_54,A_53)
      | ~ r1_tarski(C_52,B_54)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_177,plain,(
    ! [A_59] :
      ( v2_tex_2('#skF_4',A_59)
      | ~ v2_tex_2(u1_struct_0('#skF_3'),A_59)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_76,c_138])).

tff(c_181,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_39,c_177])).

tff(c_184,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_181])).

tff(c_185,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_184])).

tff(c_188,plain,
    ( ~ v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_43,c_185])).

tff(c_191,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_188])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:48:35 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.25  
% 2.08/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.25  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
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
% 2.08/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.08/1.25  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.08/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.25  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.08/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.08/1.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.08/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.08/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.08/1.25  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.08/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.25  
% 2.22/1.26  tff(f_88, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 2.22/1.26  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.22/1.26  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.22/1.26  tff(f_59, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tex_2)).
% 2.22/1.26  tff(f_39, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.22/1.26  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.22/1.26  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.22/1.26  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 2.22/1.26  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.22/1.26  tff(c_32, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.22/1.26  tff(c_34, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.22/1.26  tff(c_14, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.22/1.26  tff(c_16, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.22/1.26  tff(c_39, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 2.22/1.26  tff(c_22, plain, (![A_11]: (v2_tex_2(u1_struct_0(A_11), A_11) | ~v1_tdlat_3(A_11) | ~m1_subset_1(u1_struct_0(A_11), k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.22/1.26  tff(c_43, plain, (![A_11]: (v2_tex_2(u1_struct_0(A_11), A_11) | ~v1_tdlat_3(A_11) | ~l1_pre_topc(A_11) | v2_struct_0(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_22])).
% 2.22/1.26  tff(c_28, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.22/1.26  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.22/1.26  tff(c_18, plain, (![A_8]: (~v1_xboole_0(k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.26  tff(c_61, plain, (![A_29, B_30]: (r2_hidden(A_29, B_30) | v1_xboole_0(B_30) | ~m1_subset_1(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.22/1.26  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.22/1.26  tff(c_65, plain, (![A_29, A_1]: (r1_tarski(A_29, A_1) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_29, k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_61, c_2])).
% 2.22/1.26  tff(c_69, plain, (![A_31, A_32]: (r1_tarski(A_31, A_32) | ~m1_subset_1(A_31, k1_zfmisc_1(A_32)))), inference(negUnitSimplification, [status(thm)], [c_18, c_65])).
% 2.22/1.26  tff(c_76, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_69])).
% 2.22/1.26  tff(c_138, plain, (![C_52, A_53, B_54]: (v2_tex_2(C_52, A_53) | ~v2_tex_2(B_54, A_53) | ~r1_tarski(C_52, B_54) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.22/1.26  tff(c_177, plain, (![A_59]: (v2_tex_2('#skF_4', A_59) | ~v2_tex_2(u1_struct_0('#skF_3'), A_59) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(resolution, [status(thm)], [c_76, c_138])).
% 2.22/1.26  tff(c_181, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_39, c_177])).
% 2.22/1.26  tff(c_184, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_181])).
% 2.22/1.26  tff(c_185, plain, (~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_184])).
% 2.22/1.26  tff(c_188, plain, (~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_43, c_185])).
% 2.22/1.26  tff(c_191, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_188])).
% 2.22/1.26  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_191])).
% 2.22/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.26  
% 2.22/1.26  Inference rules
% 2.22/1.26  ----------------------
% 2.22/1.26  #Ref     : 0
% 2.22/1.26  #Sup     : 27
% 2.22/1.26  #Fact    : 0
% 2.22/1.26  #Define  : 0
% 2.22/1.26  #Split   : 0
% 2.22/1.26  #Chain   : 0
% 2.22/1.26  #Close   : 0
% 2.22/1.26  
% 2.22/1.26  Ordering : KBO
% 2.22/1.26  
% 2.22/1.26  Simplification rules
% 2.22/1.26  ----------------------
% 2.22/1.26  #Subsume      : 1
% 2.22/1.26  #Demod        : 7
% 2.22/1.26  #Tautology    : 10
% 2.22/1.26  #SimpNegUnit  : 6
% 2.22/1.26  #BackRed      : 0
% 2.22/1.26  
% 2.22/1.26  #Partial instantiations: 0
% 2.22/1.26  #Strategies tried      : 1
% 2.22/1.26  
% 2.22/1.26  Timing (in seconds)
% 2.22/1.26  ----------------------
% 2.22/1.27  Preprocessing        : 0.30
% 2.22/1.27  Parsing              : 0.16
% 2.22/1.27  CNF conversion       : 0.02
% 2.22/1.27  Main loop            : 0.21
% 2.22/1.27  Inferencing          : 0.08
% 2.22/1.27  Reduction            : 0.06
% 2.22/1.27  Demodulation         : 0.04
% 2.22/1.27  BG Simplification    : 0.01
% 2.22/1.27  Subsumption          : 0.04
% 2.22/1.27  Abstraction          : 0.01
% 2.22/1.27  MUC search           : 0.00
% 2.22/1.27  Cooper               : 0.00
% 2.22/1.27  Total                : 0.54
% 2.22/1.27  Index Insertion      : 0.00
% 2.22/1.27  Index Deletion       : 0.00
% 2.22/1.27  Index Matching       : 0.00
% 2.22/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
