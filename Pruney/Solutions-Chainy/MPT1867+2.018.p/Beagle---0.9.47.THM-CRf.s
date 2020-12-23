%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:24 EST 2020

% Result     : Theorem 7.52s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 231 expanded)
%              Number of leaves         :   33 (  94 expanded)
%              Depth                    :   14
%              Number of atoms          :  134 ( 529 expanded)
%              Number of equality atoms :   27 ( 106 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_53,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_48,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_54,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_52,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_61,plain,(
    ! [A_54] :
      ( k1_xboole_0 = A_54
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_70,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_52,c_61])).

tff(c_24,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_79,plain,(
    ! [A_15] : m1_subset_1('#skF_6',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_24])).

tff(c_91,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(A_61,B_62)
      | ~ m1_subset_1(A_61,k1_zfmisc_1(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_99,plain,(
    ! [A_15] : r1_tarski('#skF_6',A_15) ),
    inference(resolution,[status(thm)],[c_79,c_91])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_111,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(A_69,B_70) = '#skF_6'
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_16])).

tff(c_129,plain,(
    ! [A_15] : k4_xboole_0('#skF_6',A_15) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_99,c_111])).

tff(c_515,plain,(
    ! [A_116,B_117] :
      ( r1_tarski('#skF_4'(A_116,B_117),B_117)
      | v2_tex_2(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_664,plain,(
    ! [A_127] :
      ( r1_tarski('#skF_4'(A_127,'#skF_6'),'#skF_6')
      | v2_tex_2('#skF_6',A_127)
      | ~ l1_pre_topc(A_127) ) ),
    inference(resolution,[status(thm)],[c_79,c_515])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_103,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_14])).

tff(c_204,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(B_76,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_215,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | k4_xboole_0(A_6,B_7) != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_103,c_204])).

tff(c_667,plain,(
    ! [A_127] :
      ( '#skF_4'(A_127,'#skF_6') = '#skF_6'
      | k4_xboole_0('#skF_6','#skF_4'(A_127,'#skF_6')) != '#skF_6'
      | v2_tex_2('#skF_6',A_127)
      | ~ l1_pre_topc(A_127) ) ),
    inference(resolution,[status(thm)],[c_664,c_215])).

tff(c_690,plain,(
    ! [A_128] :
      ( '#skF_4'(A_128,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_667])).

tff(c_693,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_690,c_48])).

tff(c_696,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_693])).

tff(c_56,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_646,plain,(
    ! [A_125,B_126] :
      ( m1_subset_1('#skF_4'(A_125,B_126),k1_zfmisc_1(u1_struct_0(A_125)))
      | v2_tex_2(B_126,A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34,plain,(
    ! [B_26,A_24] :
      ( v3_pre_topc(B_26,A_24)
      | ~ v1_xboole_0(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2386,plain,(
    ! [A_222,B_223] :
      ( v3_pre_topc('#skF_4'(A_222,B_223),A_222)
      | ~ v1_xboole_0('#skF_4'(A_222,B_223))
      | ~ v2_pre_topc(A_222)
      | v2_tex_2(B_223,A_222)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222) ) ),
    inference(resolution,[status(thm)],[c_646,c_34])).

tff(c_2806,plain,(
    ! [A_247] :
      ( v3_pre_topc('#skF_4'(A_247,'#skF_6'),A_247)
      | ~ v1_xboole_0('#skF_4'(A_247,'#skF_6'))
      | ~ v2_pre_topc(A_247)
      | v2_tex_2('#skF_6',A_247)
      | ~ l1_pre_topc(A_247) ) ),
    inference(resolution,[status(thm)],[c_79,c_2386])).

tff(c_2809,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | ~ v1_xboole_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_pre_topc('#skF_5')
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_2806])).

tff(c_2811,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_52,c_696,c_2809])).

tff(c_2812,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2811])).

tff(c_20,plain,(
    ! [A_10] : m1_subset_1('#skF_2'(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_363,plain,(
    ! [A_90,B_91,C_92] :
      ( k9_subset_1(A_90,B_91,B_91) = B_91
      | ~ m1_subset_1(C_92,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_372,plain,(
    ! [A_90,B_91] : k9_subset_1(A_90,B_91,B_91) = B_91 ),
    inference(resolution,[status(thm)],[c_20,c_363])).

tff(c_800,plain,(
    ! [A_135,B_136,D_137] :
      ( k9_subset_1(u1_struct_0(A_135),B_136,D_137) != '#skF_4'(A_135,B_136)
      | ~ v3_pre_topc(D_137,A_135)
      | ~ m1_subset_1(D_137,k1_zfmisc_1(u1_struct_0(A_135)))
      | v2_tex_2(B_136,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_7264,plain,(
    ! [A_439,B_440] :
      ( '#skF_4'(A_439,B_440) != B_440
      | ~ v3_pre_topc(B_440,A_439)
      | ~ m1_subset_1(B_440,k1_zfmisc_1(u1_struct_0(A_439)))
      | v2_tex_2(B_440,A_439)
      | ~ m1_subset_1(B_440,k1_zfmisc_1(u1_struct_0(A_439)))
      | ~ l1_pre_topc(A_439) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_800])).

tff(c_7292,plain,(
    ! [A_439] :
      ( '#skF_4'(A_439,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_439)
      | v2_tex_2('#skF_6',A_439)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_439)))
      | ~ l1_pre_topc(A_439) ) ),
    inference(resolution,[status(thm)],[c_79,c_7264])).

tff(c_7311,plain,(
    ! [A_441] :
      ( '#skF_4'(A_441,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_441)
      | v2_tex_2('#skF_6',A_441)
      | ~ l1_pre_topc(A_441) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_7292])).

tff(c_7314,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_2812,c_7311])).

tff(c_7320,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_696,c_7314])).

tff(c_7322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_7320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:11:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.52/2.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.52/2.65  
% 7.52/2.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.52/2.66  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 7.52/2.66  
% 7.52/2.66  %Foreground sorts:
% 7.52/2.66  
% 7.52/2.66  
% 7.52/2.66  %Background operators:
% 7.52/2.66  
% 7.52/2.66  
% 7.52/2.66  %Foreground operators:
% 7.52/2.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.52/2.66  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.52/2.66  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.52/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.52/2.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.52/2.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.52/2.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.52/2.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.52/2.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.52/2.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.52/2.66  tff('#skF_5', type, '#skF_5': $i).
% 7.52/2.66  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.52/2.66  tff('#skF_6', type, '#skF_6': $i).
% 7.52/2.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.52/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.52/2.66  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.52/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.52/2.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.52/2.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.52/2.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.52/2.66  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.52/2.66  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.52/2.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.52/2.66  
% 7.68/2.67  tff(f_123, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 7.68/2.67  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.68/2.67  tff(f_59, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.68/2.67  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.68/2.67  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.68/2.67  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 7.68/2.67  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.68/2.67  tff(f_87, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tops_1)).
% 7.68/2.67  tff(f_53, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 7.68/2.67  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 7.68/2.67  tff(c_48, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.68/2.67  tff(c_54, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.68/2.67  tff(c_52, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.68/2.67  tff(c_61, plain, (![A_54]: (k1_xboole_0=A_54 | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.68/2.67  tff(c_70, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_52, c_61])).
% 7.68/2.67  tff(c_24, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.68/2.67  tff(c_79, plain, (![A_15]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_24])).
% 7.68/2.67  tff(c_91, plain, (![A_61, B_62]: (r1_tarski(A_61, B_62) | ~m1_subset_1(A_61, k1_zfmisc_1(B_62)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.68/2.67  tff(c_99, plain, (![A_15]: (r1_tarski('#skF_6', A_15))), inference(resolution, [status(thm)], [c_79, c_91])).
% 7.68/2.67  tff(c_16, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.68/2.67  tff(c_111, plain, (![A_69, B_70]: (k4_xboole_0(A_69, B_70)='#skF_6' | ~r1_tarski(A_69, B_70))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_16])).
% 7.68/2.67  tff(c_129, plain, (![A_15]: (k4_xboole_0('#skF_6', A_15)='#skF_6')), inference(resolution, [status(thm)], [c_99, c_111])).
% 7.68/2.67  tff(c_515, plain, (![A_116, B_117]: (r1_tarski('#skF_4'(A_116, B_117), B_117) | v2_tex_2(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.68/2.67  tff(c_664, plain, (![A_127]: (r1_tarski('#skF_4'(A_127, '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', A_127) | ~l1_pre_topc(A_127))), inference(resolution, [status(thm)], [c_79, c_515])).
% 7.68/2.67  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.68/2.67  tff(c_103, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_14])).
% 7.68/2.67  tff(c_204, plain, (![B_76, A_77]: (B_76=A_77 | ~r1_tarski(B_76, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.68/2.67  tff(c_215, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | k4_xboole_0(A_6, B_7)!='#skF_6')), inference(resolution, [status(thm)], [c_103, c_204])).
% 7.68/2.67  tff(c_667, plain, (![A_127]: ('#skF_4'(A_127, '#skF_6')='#skF_6' | k4_xboole_0('#skF_6', '#skF_4'(A_127, '#skF_6'))!='#skF_6' | v2_tex_2('#skF_6', A_127) | ~l1_pre_topc(A_127))), inference(resolution, [status(thm)], [c_664, c_215])).
% 7.68/2.67  tff(c_690, plain, (![A_128]: ('#skF_4'(A_128, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_128) | ~l1_pre_topc(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_667])).
% 7.68/2.67  tff(c_693, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_690, c_48])).
% 7.68/2.67  tff(c_696, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_693])).
% 7.68/2.67  tff(c_56, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.68/2.67  tff(c_646, plain, (![A_125, B_126]: (m1_subset_1('#skF_4'(A_125, B_126), k1_zfmisc_1(u1_struct_0(A_125))) | v2_tex_2(B_126, A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.68/2.67  tff(c_34, plain, (![B_26, A_24]: (v3_pre_topc(B_26, A_24) | ~v1_xboole_0(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.68/2.67  tff(c_2386, plain, (![A_222, B_223]: (v3_pre_topc('#skF_4'(A_222, B_223), A_222) | ~v1_xboole_0('#skF_4'(A_222, B_223)) | ~v2_pre_topc(A_222) | v2_tex_2(B_223, A_222) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222))), inference(resolution, [status(thm)], [c_646, c_34])).
% 7.68/2.67  tff(c_2806, plain, (![A_247]: (v3_pre_topc('#skF_4'(A_247, '#skF_6'), A_247) | ~v1_xboole_0('#skF_4'(A_247, '#skF_6')) | ~v2_pre_topc(A_247) | v2_tex_2('#skF_6', A_247) | ~l1_pre_topc(A_247))), inference(resolution, [status(thm)], [c_79, c_2386])).
% 7.68/2.67  tff(c_2809, plain, (v3_pre_topc('#skF_6', '#skF_5') | ~v1_xboole_0('#skF_4'('#skF_5', '#skF_6')) | ~v2_pre_topc('#skF_5') | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_696, c_2806])).
% 7.68/2.67  tff(c_2811, plain, (v3_pre_topc('#skF_6', '#skF_5') | v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_52, c_696, c_2809])).
% 7.68/2.67  tff(c_2812, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_2811])).
% 7.68/2.67  tff(c_20, plain, (![A_10]: (m1_subset_1('#skF_2'(A_10), A_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.68/2.67  tff(c_363, plain, (![A_90, B_91, C_92]: (k9_subset_1(A_90, B_91, B_91)=B_91 | ~m1_subset_1(C_92, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.68/2.67  tff(c_372, plain, (![A_90, B_91]: (k9_subset_1(A_90, B_91, B_91)=B_91)), inference(resolution, [status(thm)], [c_20, c_363])).
% 7.68/2.67  tff(c_800, plain, (![A_135, B_136, D_137]: (k9_subset_1(u1_struct_0(A_135), B_136, D_137)!='#skF_4'(A_135, B_136) | ~v3_pre_topc(D_137, A_135) | ~m1_subset_1(D_137, k1_zfmisc_1(u1_struct_0(A_135))) | v2_tex_2(B_136, A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.68/2.67  tff(c_7264, plain, (![A_439, B_440]: ('#skF_4'(A_439, B_440)!=B_440 | ~v3_pre_topc(B_440, A_439) | ~m1_subset_1(B_440, k1_zfmisc_1(u1_struct_0(A_439))) | v2_tex_2(B_440, A_439) | ~m1_subset_1(B_440, k1_zfmisc_1(u1_struct_0(A_439))) | ~l1_pre_topc(A_439))), inference(superposition, [status(thm), theory('equality')], [c_372, c_800])).
% 7.68/2.67  tff(c_7292, plain, (![A_439]: ('#skF_4'(A_439, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_6', A_439) | v2_tex_2('#skF_6', A_439) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_439))) | ~l1_pre_topc(A_439))), inference(resolution, [status(thm)], [c_79, c_7264])).
% 7.68/2.67  tff(c_7311, plain, (![A_441]: ('#skF_4'(A_441, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_6', A_441) | v2_tex_2('#skF_6', A_441) | ~l1_pre_topc(A_441))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_7292])).
% 7.68/2.67  tff(c_7314, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_2812, c_7311])).
% 7.68/2.67  tff(c_7320, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_696, c_7314])).
% 7.68/2.67  tff(c_7322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_7320])).
% 7.68/2.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.68/2.67  
% 7.68/2.67  Inference rules
% 7.68/2.67  ----------------------
% 7.68/2.67  #Ref     : 0
% 7.68/2.67  #Sup     : 1681
% 7.68/2.67  #Fact    : 0
% 7.68/2.67  #Define  : 0
% 7.68/2.67  #Split   : 10
% 7.68/2.67  #Chain   : 0
% 7.68/2.67  #Close   : 0
% 7.68/2.67  
% 7.68/2.67  Ordering : KBO
% 7.68/2.67  
% 7.68/2.67  Simplification rules
% 7.68/2.67  ----------------------
% 7.68/2.67  #Subsume      : 513
% 7.68/2.67  #Demod        : 1022
% 7.68/2.67  #Tautology    : 477
% 7.68/2.67  #SimpNegUnit  : 38
% 7.68/2.67  #BackRed      : 4
% 7.68/2.67  
% 7.68/2.67  #Partial instantiations: 0
% 7.68/2.67  #Strategies tried      : 1
% 7.68/2.67  
% 7.68/2.67  Timing (in seconds)
% 7.68/2.67  ----------------------
% 7.68/2.67  Preprocessing        : 0.31
% 7.68/2.67  Parsing              : 0.17
% 7.68/2.67  CNF conversion       : 0.02
% 7.68/2.67  Main loop            : 1.60
% 7.68/2.67  Inferencing          : 0.51
% 7.68/2.67  Reduction            : 0.47
% 7.68/2.67  Demodulation         : 0.32
% 7.68/2.68  BG Simplification    : 0.05
% 7.68/2.68  Subsumption          : 0.46
% 7.68/2.68  Abstraction          : 0.07
% 7.68/2.68  MUC search           : 0.00
% 7.68/2.68  Cooper               : 0.00
% 7.68/2.68  Total                : 1.94
% 7.68/2.68  Index Insertion      : 0.00
% 7.68/2.68  Index Deletion       : 0.00
% 7.68/2.68  Index Matching       : 0.00
% 7.68/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
