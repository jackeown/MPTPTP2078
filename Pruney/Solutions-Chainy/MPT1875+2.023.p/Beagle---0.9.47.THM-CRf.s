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
% DateTime   : Thu Dec  3 10:29:49 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 108 expanded)
%              Number of leaves         :   25 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   95 ( 231 expanded)
%              Number of equality atoms :   10 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_tex_2(B,A)
                  | v2_tex_2(C,A) )
               => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_22,plain,(
    ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_33,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_14,plain,(
    ! [A_10] :
      ( v2_tex_2(u1_struct_0(A_10),A_10)
      | ~ v1_tdlat_3(A_10)
      | ~ m1_subset_1(u1_struct_0(A_10),k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_37,plain,(
    ! [A_10] :
      ( v2_tex_2(u1_struct_0(A_10),A_10)
      | ~ v1_tdlat_3(A_10)
      | ~ l1_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_14])).

tff(c_91,plain,(
    ! [A_33,B_34,C_35] :
      ( k9_subset_1(A_33,B_34,C_35) = k3_xboole_0(B_34,C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_99,plain,(
    ! [B_34] : k9_subset_1(u1_struct_0('#skF_1'),B_34,'#skF_2') = k3_xboole_0(B_34,'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_91])).

tff(c_128,plain,(
    ! [B_42,A_43,C_44] :
      ( ~ v2_tex_2(B_42,A_43)
      | v2_tex_2(k9_subset_1(u1_struct_0(A_43),B_42,C_44),A_43)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_131,plain,(
    ! [B_34] :
      ( ~ v2_tex_2(B_34,'#skF_1')
      | v2_tex_2(k3_xboole_0(B_34,'#skF_2'),'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_128])).

tff(c_140,plain,(
    ! [B_45] :
      ( ~ v2_tex_2(B_45,'#skF_1')
      | v2_tex_2(k3_xboole_0(B_45,'#skF_2'),'#skF_1')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_131])).

tff(c_156,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_1'),'#skF_1')
    | v2_tex_2(k3_xboole_0(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_33,c_140])).

tff(c_157,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_160,plain,
    ( ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_37,c_157])).

tff(c_163,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_160])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_163])).

tff(c_167,plain,(
    v2_tex_2(u1_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_48,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_55,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_48])).

tff(c_58,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_55,c_58])).

tff(c_100,plain,(
    ! [A_4,B_34] : k9_subset_1(A_4,B_34,A_4) = k3_xboole_0(B_34,A_4) ),
    inference(resolution,[status(thm)],[c_33,c_91])).

tff(c_168,plain,(
    ! [C_46,A_47,B_48] :
      ( ~ v2_tex_2(C_46,A_47)
      | v2_tex_2(k9_subset_1(u1_struct_0(A_47),B_48,C_46),A_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_175,plain,(
    ! [A_47,B_34] :
      ( ~ v2_tex_2(u1_struct_0(A_47),A_47)
      | v2_tex_2(k3_xboole_0(B_34,u1_struct_0(A_47)),A_47)
      | ~ m1_subset_1(u1_struct_0(A_47),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_168])).

tff(c_208,plain,(
    ! [A_52,B_53] :
      ( ~ v2_tex_2(u1_struct_0(A_52),A_52)
      | v2_tex_2(k3_xboole_0(B_53,u1_struct_0(A_52)),A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_175])).

tff(c_211,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_1'),'#skF_1')
    | v2_tex_2('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_208])).

tff(c_217,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_167,c_211])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:36:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.29  
% 2.02/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.30  %$ v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.02/1.30  
% 2.02/1.30  %Foreground sorts:
% 2.02/1.30  
% 2.02/1.30  
% 2.02/1.30  %Background operators:
% 2.02/1.30  
% 2.02/1.30  
% 2.02/1.30  %Foreground operators:
% 2.02/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.02/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.02/1.30  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.02/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.30  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.02/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.02/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.02/1.30  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.02/1.30  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.02/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.30  
% 2.02/1.31  tff(f_84, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 2.02/1.31  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.02/1.31  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.02/1.31  tff(f_55, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tex_2)).
% 2.02/1.31  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.02/1.31  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 2.02/1.31  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.02/1.31  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.02/1.31  tff(c_22, plain, (~v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.31  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.31  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.31  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.31  tff(c_28, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.31  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.31  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.31  tff(c_33, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.02/1.31  tff(c_14, plain, (![A_10]: (v2_tex_2(u1_struct_0(A_10), A_10) | ~v1_tdlat_3(A_10) | ~m1_subset_1(u1_struct_0(A_10), k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.02/1.31  tff(c_37, plain, (![A_10]: (v2_tex_2(u1_struct_0(A_10), A_10) | ~v1_tdlat_3(A_10) | ~l1_pre_topc(A_10) | v2_struct_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_14])).
% 2.02/1.31  tff(c_91, plain, (![A_33, B_34, C_35]: (k9_subset_1(A_33, B_34, C_35)=k3_xboole_0(B_34, C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.02/1.31  tff(c_99, plain, (![B_34]: (k9_subset_1(u1_struct_0('#skF_1'), B_34, '#skF_2')=k3_xboole_0(B_34, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_91])).
% 2.02/1.31  tff(c_128, plain, (![B_42, A_43, C_44]: (~v2_tex_2(B_42, A_43) | v2_tex_2(k9_subset_1(u1_struct_0(A_43), B_42, C_44), A_43) | ~m1_subset_1(C_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.02/1.31  tff(c_131, plain, (![B_34]: (~v2_tex_2(B_34, '#skF_1') | v2_tex_2(k3_xboole_0(B_34, '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_128])).
% 2.02/1.31  tff(c_140, plain, (![B_45]: (~v2_tex_2(B_45, '#skF_1') | v2_tex_2(k3_xboole_0(B_45, '#skF_2'), '#skF_1') | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_131])).
% 2.02/1.31  tff(c_156, plain, (~v2_tex_2(u1_struct_0('#skF_1'), '#skF_1') | v2_tex_2(k3_xboole_0(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_33, c_140])).
% 2.02/1.31  tff(c_157, plain, (~v2_tex_2(u1_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_156])).
% 2.02/1.31  tff(c_160, plain, (~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_37, c_157])).
% 2.02/1.31  tff(c_163, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_160])).
% 2.02/1.31  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_163])).
% 2.02/1.31  tff(c_167, plain, (v2_tex_2(u1_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_156])).
% 2.02/1.31  tff(c_48, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.31  tff(c_55, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_48])).
% 2.02/1.31  tff(c_58, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.31  tff(c_66, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(resolution, [status(thm)], [c_55, c_58])).
% 2.02/1.31  tff(c_100, plain, (![A_4, B_34]: (k9_subset_1(A_4, B_34, A_4)=k3_xboole_0(B_34, A_4))), inference(resolution, [status(thm)], [c_33, c_91])).
% 2.02/1.31  tff(c_168, plain, (![C_46, A_47, B_48]: (~v2_tex_2(C_46, A_47) | v2_tex_2(k9_subset_1(u1_struct_0(A_47), B_48, C_46), A_47) | ~m1_subset_1(C_46, k1_zfmisc_1(u1_struct_0(A_47))) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.02/1.31  tff(c_175, plain, (![A_47, B_34]: (~v2_tex_2(u1_struct_0(A_47), A_47) | v2_tex_2(k3_xboole_0(B_34, u1_struct_0(A_47)), A_47) | ~m1_subset_1(u1_struct_0(A_47), k1_zfmisc_1(u1_struct_0(A_47))) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(superposition, [status(thm), theory('equality')], [c_100, c_168])).
% 2.02/1.31  tff(c_208, plain, (![A_52, B_53]: (~v2_tex_2(u1_struct_0(A_52), A_52) | v2_tex_2(k3_xboole_0(B_53, u1_struct_0(A_52)), A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_175])).
% 2.02/1.31  tff(c_211, plain, (~v2_tex_2(u1_struct_0('#skF_1'), '#skF_1') | v2_tex_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_66, c_208])).
% 2.02/1.31  tff(c_217, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_167, c_211])).
% 2.02/1.31  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_217])).
% 2.02/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.31  
% 2.02/1.31  Inference rules
% 2.02/1.31  ----------------------
% 2.02/1.31  #Ref     : 0
% 2.02/1.31  #Sup     : 35
% 2.02/1.31  #Fact    : 0
% 2.02/1.31  #Define  : 0
% 2.02/1.31  #Split   : 1
% 2.02/1.31  #Chain   : 0
% 2.02/1.31  #Close   : 0
% 2.02/1.31  
% 2.02/1.31  Ordering : KBO
% 2.02/1.31  
% 2.02/1.31  Simplification rules
% 2.02/1.31  ----------------------
% 2.02/1.31  #Subsume      : 4
% 2.02/1.31  #Demod        : 23
% 2.02/1.31  #Tautology    : 16
% 2.02/1.31  #SimpNegUnit  : 6
% 2.02/1.31  #BackRed      : 0
% 2.02/1.31  
% 2.02/1.31  #Partial instantiations: 0
% 2.02/1.31  #Strategies tried      : 1
% 2.02/1.31  
% 2.02/1.31  Timing (in seconds)
% 2.02/1.31  ----------------------
% 2.02/1.31  Preprocessing        : 0.33
% 2.02/1.31  Parsing              : 0.18
% 2.02/1.31  CNF conversion       : 0.02
% 2.02/1.31  Main loop            : 0.18
% 2.02/1.31  Inferencing          : 0.07
% 2.02/1.31  Reduction            : 0.06
% 2.02/1.31  Demodulation         : 0.04
% 2.02/1.31  BG Simplification    : 0.01
% 2.02/1.31  Subsumption          : 0.03
% 2.02/1.32  Abstraction          : 0.01
% 2.02/1.32  MUC search           : 0.00
% 2.02/1.32  Cooper               : 0.00
% 2.02/1.32  Total                : 0.54
% 2.02/1.32  Index Insertion      : 0.00
% 2.02/1.32  Index Deletion       : 0.00
% 2.02/1.32  Index Matching       : 0.00
% 2.02/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
