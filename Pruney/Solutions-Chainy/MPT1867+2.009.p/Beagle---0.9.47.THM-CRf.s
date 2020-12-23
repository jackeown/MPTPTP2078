%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:23 EST 2020

% Result     : Theorem 27.46s
% Output     : CNFRefutation 27.46s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 115 expanded)
%              Number of leaves         :   34 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  127 ( 238 expanded)
%              Number of equality atoms :   24 (  38 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_105,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_54,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_52,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_58,plain,(
    ! [A_59] :
      ( k1_xboole_0 = A_59
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_62,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_50,c_58])).

tff(c_22,plain,(
    ! [A_20] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,(
    ! [A_20] : m1_subset_1('#skF_6',k1_zfmisc_1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_22])).

tff(c_123,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(A_69,B_70)
      | ~ m1_subset_1(A_69,k1_zfmisc_1(B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_127,plain,(
    ! [A_20] : r1_tarski('#skF_6',A_20) ),
    inference(resolution,[status(thm)],[c_64,c_123])).

tff(c_144,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(A_76,B_77) = A_76
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_155,plain,(
    ! [A_20] : k3_xboole_0('#skF_6',A_20) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_127,c_144])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_703,plain,(
    ! [A_127,B_128] :
      ( r1_tarski('#skF_4'(A_127,B_128),B_128)
      | v2_tex_2(B_128,A_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3622,plain,(
    ! [A_225] :
      ( r1_tarski('#skF_4'(A_225,'#skF_6'),'#skF_6')
      | v2_tex_2('#skF_6',A_225)
      | ~ l1_pre_topc(A_225) ) ),
    inference(resolution,[status(thm)],[c_64,c_703])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3635,plain,(
    ! [A_225] :
      ( k3_xboole_0('#skF_4'(A_225,'#skF_6'),'#skF_6') = '#skF_4'(A_225,'#skF_6')
      | v2_tex_2('#skF_6',A_225)
      | ~ l1_pre_topc(A_225) ) ),
    inference(resolution,[status(thm)],[c_3622,c_18])).

tff(c_3660,plain,(
    ! [A_227] :
      ( '#skF_4'(A_227,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_227)
      | ~ l1_pre_topc(A_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_2,c_3635])).

tff(c_46,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3663,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_3660,c_46])).

tff(c_3666,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3663])).

tff(c_231,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_2'(A_82,B_83),A_82)
      | r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_240,plain,(
    ! [A_82,B_83] :
      ( ~ v1_xboole_0(A_82)
      | r1_tarski(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_231,c_4])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_601,plain,(
    ! [B_120,A_121] :
      ( v3_pre_topc(B_120,A_121)
      | ~ v1_xboole_0(B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2801,plain,(
    ! [A_189,A_190] :
      ( v3_pre_topc(A_189,A_190)
      | ~ v1_xboole_0(A_189)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | ~ r1_tarski(A_189,u1_struct_0(A_190)) ) ),
    inference(resolution,[status(thm)],[c_26,c_601])).

tff(c_2832,plain,(
    ! [A_82,A_190] :
      ( v3_pre_topc(A_82,A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | ~ v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_240,c_2801])).

tff(c_480,plain,(
    ! [A_104,B_105,C_106] :
      ( k9_subset_1(A_104,B_105,B_105) = B_105
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_486,plain,(
    ! [A_20,B_105] : k9_subset_1(A_20,B_105,B_105) = B_105 ),
    inference(resolution,[status(thm)],[c_64,c_480])).

tff(c_1313,plain,(
    ! [A_154,B_155,D_156] :
      ( k9_subset_1(u1_struct_0(A_154),B_155,D_156) != '#skF_4'(A_154,B_155)
      | ~ v3_pre_topc(D_156,A_154)
      | ~ m1_subset_1(D_156,k1_zfmisc_1(u1_struct_0(A_154)))
      | v2_tex_2(B_155,A_154)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_70450,plain,(
    ! [A_1019,B_1020] :
      ( '#skF_4'(A_1019,B_1020) != B_1020
      | ~ v3_pre_topc(B_1020,A_1019)
      | ~ m1_subset_1(B_1020,k1_zfmisc_1(u1_struct_0(A_1019)))
      | v2_tex_2(B_1020,A_1019)
      | ~ m1_subset_1(B_1020,k1_zfmisc_1(u1_struct_0(A_1019)))
      | ~ l1_pre_topc(A_1019) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_1313])).

tff(c_70481,plain,(
    ! [A_1019] :
      ( '#skF_4'(A_1019,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_1019)
      | v2_tex_2('#skF_6',A_1019)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_1019)))
      | ~ l1_pre_topc(A_1019) ) ),
    inference(resolution,[status(thm)],[c_64,c_70450])).

tff(c_123193,plain,(
    ! [A_1410] :
      ( '#skF_4'(A_1410,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_1410)
      | v2_tex_2('#skF_6',A_1410)
      | ~ l1_pre_topc(A_1410) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_70481])).

tff(c_123197,plain,(
    ! [A_190] :
      ( '#skF_4'(A_190,'#skF_6') != '#skF_6'
      | v2_tex_2('#skF_6',A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2832,c_123193])).

tff(c_123205,plain,(
    ! [A_1411] :
      ( '#skF_4'(A_1411,'#skF_6') != '#skF_6'
      | v2_tex_2('#skF_6',A_1411)
      | ~ l1_pre_topc(A_1411)
      | ~ v2_pre_topc(A_1411) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_123197])).

tff(c_123208,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_123205,c_46])).

tff(c_123212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3666,c_123208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.46/18.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.46/18.75  
% 27.46/18.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.46/18.75  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 27.46/18.75  
% 27.46/18.75  %Foreground sorts:
% 27.46/18.75  
% 27.46/18.75  
% 27.46/18.75  %Background operators:
% 27.46/18.75  
% 27.46/18.75  
% 27.46/18.75  %Foreground operators:
% 27.46/18.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 27.46/18.75  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 27.46/18.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.46/18.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.46/18.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 27.46/18.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 27.46/18.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 27.46/18.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.46/18.75  tff('#skF_5', type, '#skF_5': $i).
% 27.46/18.75  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 27.46/18.75  tff('#skF_6', type, '#skF_6': $i).
% 27.46/18.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 27.46/18.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.46/18.75  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 27.46/18.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.46/18.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 27.46/18.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 27.46/18.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.46/18.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 27.46/18.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 27.46/18.75  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 27.46/18.75  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 27.46/18.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.46/18.75  
% 27.46/18.77  tff(f_120, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 27.46/18.77  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 27.46/18.77  tff(f_56, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 27.46/18.77  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 27.46/18.77  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 27.46/18.77  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 27.46/18.77  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 27.46/18.77  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 27.46/18.77  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 27.46/18.77  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tops_1)).
% 27.46/18.77  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 27.46/18.77  tff(c_54, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 27.46/18.77  tff(c_52, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 27.46/18.77  tff(c_50, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_120])).
% 27.46/18.77  tff(c_58, plain, (![A_59]: (k1_xboole_0=A_59 | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.46/18.77  tff(c_62, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_50, c_58])).
% 27.46/18.77  tff(c_22, plain, (![A_20]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.46/18.77  tff(c_64, plain, (![A_20]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_22])).
% 27.46/18.77  tff(c_123, plain, (![A_69, B_70]: (r1_tarski(A_69, B_70) | ~m1_subset_1(A_69, k1_zfmisc_1(B_70)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 27.46/18.77  tff(c_127, plain, (![A_20]: (r1_tarski('#skF_6', A_20))), inference(resolution, [status(thm)], [c_64, c_123])).
% 27.46/18.77  tff(c_144, plain, (![A_76, B_77]: (k3_xboole_0(A_76, B_77)=A_76 | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_50])).
% 27.46/18.77  tff(c_155, plain, (![A_20]: (k3_xboole_0('#skF_6', A_20)='#skF_6')), inference(resolution, [status(thm)], [c_127, c_144])).
% 27.46/18.77  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 27.46/18.77  tff(c_703, plain, (![A_127, B_128]: (r1_tarski('#skF_4'(A_127, B_128), B_128) | v2_tex_2(B_128, A_127) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_105])).
% 27.46/18.77  tff(c_3622, plain, (![A_225]: (r1_tarski('#skF_4'(A_225, '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', A_225) | ~l1_pre_topc(A_225))), inference(resolution, [status(thm)], [c_64, c_703])).
% 27.46/18.77  tff(c_18, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 27.46/18.77  tff(c_3635, plain, (![A_225]: (k3_xboole_0('#skF_4'(A_225, '#skF_6'), '#skF_6')='#skF_4'(A_225, '#skF_6') | v2_tex_2('#skF_6', A_225) | ~l1_pre_topc(A_225))), inference(resolution, [status(thm)], [c_3622, c_18])).
% 27.46/18.77  tff(c_3660, plain, (![A_227]: ('#skF_4'(A_227, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_227) | ~l1_pre_topc(A_227))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_2, c_3635])).
% 27.46/18.77  tff(c_46, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 27.46/18.77  tff(c_3663, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_3660, c_46])).
% 27.46/18.77  tff(c_3666, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3663])).
% 27.46/18.77  tff(c_231, plain, (![A_82, B_83]: (r2_hidden('#skF_2'(A_82, B_83), A_82) | r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_40])).
% 27.46/18.77  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.46/18.77  tff(c_240, plain, (![A_82, B_83]: (~v1_xboole_0(A_82) | r1_tarski(A_82, B_83))), inference(resolution, [status(thm)], [c_231, c_4])).
% 27.46/18.77  tff(c_26, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 27.46/18.77  tff(c_601, plain, (![B_120, A_121]: (v3_pre_topc(B_120, A_121) | ~v1_xboole_0(B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.46/18.77  tff(c_2801, plain, (![A_189, A_190]: (v3_pre_topc(A_189, A_190) | ~v1_xboole_0(A_189) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | ~r1_tarski(A_189, u1_struct_0(A_190)))), inference(resolution, [status(thm)], [c_26, c_601])).
% 27.46/18.77  tff(c_2832, plain, (![A_82, A_190]: (v3_pre_topc(A_82, A_190) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | ~v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_240, c_2801])).
% 27.46/18.77  tff(c_480, plain, (![A_104, B_105, C_106]: (k9_subset_1(A_104, B_105, B_105)=B_105 | ~m1_subset_1(C_106, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 27.46/18.77  tff(c_486, plain, (![A_20, B_105]: (k9_subset_1(A_20, B_105, B_105)=B_105)), inference(resolution, [status(thm)], [c_64, c_480])).
% 27.46/18.77  tff(c_1313, plain, (![A_154, B_155, D_156]: (k9_subset_1(u1_struct_0(A_154), B_155, D_156)!='#skF_4'(A_154, B_155) | ~v3_pre_topc(D_156, A_154) | ~m1_subset_1(D_156, k1_zfmisc_1(u1_struct_0(A_154))) | v2_tex_2(B_155, A_154) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_105])).
% 27.46/18.77  tff(c_70450, plain, (![A_1019, B_1020]: ('#skF_4'(A_1019, B_1020)!=B_1020 | ~v3_pre_topc(B_1020, A_1019) | ~m1_subset_1(B_1020, k1_zfmisc_1(u1_struct_0(A_1019))) | v2_tex_2(B_1020, A_1019) | ~m1_subset_1(B_1020, k1_zfmisc_1(u1_struct_0(A_1019))) | ~l1_pre_topc(A_1019))), inference(superposition, [status(thm), theory('equality')], [c_486, c_1313])).
% 27.46/18.77  tff(c_70481, plain, (![A_1019]: ('#skF_4'(A_1019, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_6', A_1019) | v2_tex_2('#skF_6', A_1019) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_1019))) | ~l1_pre_topc(A_1019))), inference(resolution, [status(thm)], [c_64, c_70450])).
% 27.46/18.77  tff(c_123193, plain, (![A_1410]: ('#skF_4'(A_1410, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_6', A_1410) | v2_tex_2('#skF_6', A_1410) | ~l1_pre_topc(A_1410))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_70481])).
% 27.46/18.77  tff(c_123197, plain, (![A_190]: ('#skF_4'(A_190, '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', A_190) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_2832, c_123193])).
% 27.46/18.77  tff(c_123205, plain, (![A_1411]: ('#skF_4'(A_1411, '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', A_1411) | ~l1_pre_topc(A_1411) | ~v2_pre_topc(A_1411))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_123197])).
% 27.46/18.77  tff(c_123208, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_123205, c_46])).
% 27.46/18.77  tff(c_123212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3666, c_123208])).
% 27.46/18.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.46/18.77  
% 27.46/18.77  Inference rules
% 27.46/18.77  ----------------------
% 27.46/18.77  #Ref     : 0
% 27.46/18.77  #Sup     : 33058
% 27.46/18.77  #Fact    : 0
% 27.46/18.77  #Define  : 0
% 27.46/18.77  #Split   : 10
% 27.46/18.77  #Chain   : 0
% 27.46/18.77  #Close   : 0
% 27.46/18.77  
% 27.46/18.77  Ordering : KBO
% 27.46/18.77  
% 27.46/18.77  Simplification rules
% 27.46/18.77  ----------------------
% 27.46/18.77  #Subsume      : 16704
% 27.46/18.77  #Demod        : 21877
% 27.46/18.77  #Tautology    : 9902
% 27.46/18.77  #SimpNegUnit  : 103
% 27.46/18.77  #BackRed      : 4
% 27.46/18.77  
% 27.46/18.77  #Partial instantiations: 0
% 27.46/18.77  #Strategies tried      : 1
% 27.46/18.77  
% 27.46/18.77  Timing (in seconds)
% 27.46/18.77  ----------------------
% 27.46/18.77  Preprocessing        : 0.29
% 27.46/18.77  Parsing              : 0.16
% 27.46/18.77  CNF conversion       : 0.02
% 27.46/18.77  Main loop            : 17.65
% 27.46/18.77  Inferencing          : 2.43
% 27.46/18.77  Reduction            : 6.76
% 27.46/18.77  Demodulation         : 5.67
% 27.46/18.77  BG Simplification    : 0.22
% 27.46/18.77  Subsumption          : 7.27
% 27.46/18.77  Abstraction          : 0.42
% 27.46/18.77  MUC search           : 0.00
% 27.46/18.77  Cooper               : 0.00
% 27.46/18.77  Total                : 17.98
% 27.46/18.77  Index Insertion      : 0.00
% 27.46/18.77  Index Deletion       : 0.00
% 27.46/18.77  Index Matching       : 0.00
% 27.46/18.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
