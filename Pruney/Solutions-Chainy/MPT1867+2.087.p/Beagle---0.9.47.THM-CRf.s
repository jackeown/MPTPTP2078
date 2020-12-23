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
% DateTime   : Thu Dec  3 10:29:34 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 205 expanded)
%              Number of leaves         :   34 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  129 ( 415 expanded)
%              Number of equality atoms :   26 (  77 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_100,axiom,(
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

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_37,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_34,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_40,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_38,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_46,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_46])).

tff(c_12,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    ! [A_11] : m1_subset_1('#skF_5',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_12])).

tff(c_233,plain,(
    ! [A_95,B_96] :
      ( r1_tarski('#skF_3'(A_95,B_96),B_96)
      | v2_tex_2(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_242,plain,(
    ! [A_97] :
      ( r1_tarski('#skF_3'(A_97,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_52,c_233])).

tff(c_6,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_65,plain,(
    ! [A_4] :
      ( A_4 = '#skF_5'
      | ~ r1_tarski(A_4,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_6])).

tff(c_247,plain,(
    ! [A_98] :
      ( '#skF_3'(A_98,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_242,c_65])).

tff(c_250,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_247,c_34])).

tff(c_253,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_250])).

tff(c_42,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_141,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(k1_tops_1(A_75,B_76),B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_162,plain,(
    ! [A_79] :
      ( r1_tarski(k1_tops_1(A_79,'#skF_5'),'#skF_5')
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_52,c_141])).

tff(c_167,plain,(
    ! [A_80] :
      ( k1_tops_1(A_80,'#skF_5') = '#skF_5'
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_162,c_65])).

tff(c_171,plain,(
    k1_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_40,c_167])).

tff(c_207,plain,(
    ! [A_88,B_89] :
      ( v3_pre_topc(k1_tops_1(A_88,B_89),A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_216,plain,(
    ! [A_90] :
      ( v3_pre_topc(k1_tops_1(A_90,'#skF_5'),A_90)
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_52,c_207])).

tff(c_219,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_216])).

tff(c_221,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_219])).

tff(c_4,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_67,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | A_2 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4])).

tff(c_92,plain,(
    ! [A_65,B_66,C_67] :
      ( k9_subset_1(A_65,B_66,C_67) = k3_xboole_0(B_66,C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_99,plain,(
    ! [A_68,B_69] : k9_subset_1(A_68,B_69,'#skF_5') = k3_xboole_0(B_69,'#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_92])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k9_subset_1(A_5,B_6,C_7),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_105,plain,(
    ! [B_69,A_68] :
      ( m1_subset_1(k3_xboole_0(B_69,'#skF_5'),k1_zfmisc_1(A_68))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_8])).

tff(c_113,plain,(
    ! [B_70,A_71] : m1_subset_1(k3_xboole_0(B_70,'#skF_5'),k1_zfmisc_1(A_71)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_105])).

tff(c_16,plain,(
    ! [C_17,B_16,A_15] :
      ( ~ v1_xboole_0(C_17)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(C_17))
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_122,plain,(
    ! [A_71,A_15,B_70] :
      ( ~ v1_xboole_0(A_71)
      | ~ r2_hidden(A_15,k3_xboole_0(B_70,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_113,c_16])).

tff(c_124,plain,(
    ! [A_72,B_73] : ~ r2_hidden(A_72,k3_xboole_0(B_73,'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_129,plain,(
    ! [B_73] : k3_xboole_0(B_73,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_67,c_124])).

tff(c_98,plain,(
    ! [A_11,B_66] : k9_subset_1(A_11,B_66,'#skF_5') = k3_xboole_0(B_66,'#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_92])).

tff(c_132,plain,(
    ! [A_11,B_66] : k9_subset_1(A_11,B_66,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_98])).

tff(c_486,plain,(
    ! [A_135,B_136,D_137] :
      ( k9_subset_1(u1_struct_0(A_135),B_136,D_137) != '#skF_3'(A_135,B_136)
      | ~ v3_pre_topc(D_137,A_135)
      | ~ m1_subset_1(D_137,k1_zfmisc_1(u1_struct_0(A_135)))
      | v2_tex_2(B_136,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_492,plain,(
    ! [A_135,B_66] :
      ( '#skF_3'(A_135,B_66) != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_135)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_135)))
      | v2_tex_2(B_66,A_135)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_486])).

tff(c_495,plain,(
    ! [A_138,B_139] :
      ( '#skF_3'(A_138,B_139) != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_138)
      | v2_tex_2(B_139,A_138)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_492])).

tff(c_515,plain,(
    ! [A_140] :
      ( '#skF_3'(A_140,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_140)
      | v2_tex_2('#skF_5',A_140)
      | ~ l1_pre_topc(A_140) ) ),
    inference(resolution,[status(thm)],[c_52,c_495])).

tff(c_518,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_221,c_515])).

tff(c_521,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_253,c_518])).

tff(c_523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_521])).

tff(c_524,plain,(
    ! [A_71] : ~ v1_xboole_0(A_71) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_524,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:05:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.38  
% 2.53/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.38  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.53/1.38  
% 2.53/1.38  %Foreground sorts:
% 2.53/1.38  
% 2.53/1.38  
% 2.53/1.38  %Background operators:
% 2.53/1.38  
% 2.53/1.38  
% 2.53/1.38  %Foreground operators:
% 2.53/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.53/1.38  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.53/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.53/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.53/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.53/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.53/1.38  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.53/1.38  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.53/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.53/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.53/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.53/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.53/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.53/1.38  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.53/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.38  
% 2.53/1.40  tff(f_115, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.53/1.40  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.53/1.40  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.53/1.40  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 2.53/1.40  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.53/1.40  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.53/1.40  tff(f_72, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.53/1.40  tff(f_37, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.53/1.40  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.53/1.40  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.53/1.40  tff(f_64, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.53/1.40  tff(c_34, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.53/1.40  tff(c_40, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.53/1.40  tff(c_38, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.53/1.40  tff(c_46, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.53/1.40  tff(c_50, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_38, c_46])).
% 2.53/1.40  tff(c_12, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.53/1.40  tff(c_52, plain, (![A_11]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_12])).
% 2.53/1.40  tff(c_233, plain, (![A_95, B_96]: (r1_tarski('#skF_3'(A_95, B_96), B_96) | v2_tex_2(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.53/1.40  tff(c_242, plain, (![A_97]: (r1_tarski('#skF_3'(A_97, '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', A_97) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_52, c_233])).
% 2.53/1.40  tff(c_6, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.53/1.40  tff(c_65, plain, (![A_4]: (A_4='#skF_5' | ~r1_tarski(A_4, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_6])).
% 2.53/1.40  tff(c_247, plain, (![A_98]: ('#skF_3'(A_98, '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_98) | ~l1_pre_topc(A_98))), inference(resolution, [status(thm)], [c_242, c_65])).
% 2.53/1.40  tff(c_250, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_247, c_34])).
% 2.53/1.40  tff(c_253, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_250])).
% 2.53/1.40  tff(c_42, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.53/1.40  tff(c_141, plain, (![A_75, B_76]: (r1_tarski(k1_tops_1(A_75, B_76), B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.53/1.40  tff(c_162, plain, (![A_79]: (r1_tarski(k1_tops_1(A_79, '#skF_5'), '#skF_5') | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_52, c_141])).
% 2.53/1.40  tff(c_167, plain, (![A_80]: (k1_tops_1(A_80, '#skF_5')='#skF_5' | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_162, c_65])).
% 2.53/1.40  tff(c_171, plain, (k1_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_40, c_167])).
% 2.53/1.40  tff(c_207, plain, (![A_88, B_89]: (v3_pre_topc(k1_tops_1(A_88, B_89), A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.53/1.40  tff(c_216, plain, (![A_90]: (v3_pre_topc(k1_tops_1(A_90, '#skF_5'), A_90) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90))), inference(resolution, [status(thm)], [c_52, c_207])).
% 2.53/1.40  tff(c_219, plain, (v3_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_171, c_216])).
% 2.53/1.40  tff(c_221, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_219])).
% 2.53/1.40  tff(c_4, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.40  tff(c_67, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | A_2='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4])).
% 2.53/1.40  tff(c_92, plain, (![A_65, B_66, C_67]: (k9_subset_1(A_65, B_66, C_67)=k3_xboole_0(B_66, C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.53/1.40  tff(c_99, plain, (![A_68, B_69]: (k9_subset_1(A_68, B_69, '#skF_5')=k3_xboole_0(B_69, '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_92])).
% 2.53/1.40  tff(c_8, plain, (![A_5, B_6, C_7]: (m1_subset_1(k9_subset_1(A_5, B_6, C_7), k1_zfmisc_1(A_5)) | ~m1_subset_1(C_7, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.53/1.40  tff(c_105, plain, (![B_69, A_68]: (m1_subset_1(k3_xboole_0(B_69, '#skF_5'), k1_zfmisc_1(A_68)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_99, c_8])).
% 2.53/1.40  tff(c_113, plain, (![B_70, A_71]: (m1_subset_1(k3_xboole_0(B_70, '#skF_5'), k1_zfmisc_1(A_71)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_105])).
% 2.53/1.40  tff(c_16, plain, (![C_17, B_16, A_15]: (~v1_xboole_0(C_17) | ~m1_subset_1(B_16, k1_zfmisc_1(C_17)) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.53/1.40  tff(c_122, plain, (![A_71, A_15, B_70]: (~v1_xboole_0(A_71) | ~r2_hidden(A_15, k3_xboole_0(B_70, '#skF_5')))), inference(resolution, [status(thm)], [c_113, c_16])).
% 2.53/1.40  tff(c_124, plain, (![A_72, B_73]: (~r2_hidden(A_72, k3_xboole_0(B_73, '#skF_5')))), inference(splitLeft, [status(thm)], [c_122])).
% 2.53/1.40  tff(c_129, plain, (![B_73]: (k3_xboole_0(B_73, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_67, c_124])).
% 2.53/1.40  tff(c_98, plain, (![A_11, B_66]: (k9_subset_1(A_11, B_66, '#skF_5')=k3_xboole_0(B_66, '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_92])).
% 2.53/1.40  tff(c_132, plain, (![A_11, B_66]: (k9_subset_1(A_11, B_66, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_98])).
% 2.53/1.40  tff(c_486, plain, (![A_135, B_136, D_137]: (k9_subset_1(u1_struct_0(A_135), B_136, D_137)!='#skF_3'(A_135, B_136) | ~v3_pre_topc(D_137, A_135) | ~m1_subset_1(D_137, k1_zfmisc_1(u1_struct_0(A_135))) | v2_tex_2(B_136, A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.53/1.40  tff(c_492, plain, (![A_135, B_66]: ('#skF_3'(A_135, B_66)!='#skF_5' | ~v3_pre_topc('#skF_5', A_135) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_135))) | v2_tex_2(B_66, A_135) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(superposition, [status(thm), theory('equality')], [c_132, c_486])).
% 2.53/1.40  tff(c_495, plain, (![A_138, B_139]: ('#skF_3'(A_138, B_139)!='#skF_5' | ~v3_pre_topc('#skF_5', A_138) | v2_tex_2(B_139, A_138) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_492])).
% 2.53/1.40  tff(c_515, plain, (![A_140]: ('#skF_3'(A_140, '#skF_5')!='#skF_5' | ~v3_pre_topc('#skF_5', A_140) | v2_tex_2('#skF_5', A_140) | ~l1_pre_topc(A_140))), inference(resolution, [status(thm)], [c_52, c_495])).
% 2.53/1.40  tff(c_518, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_221, c_515])).
% 2.53/1.40  tff(c_521, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_253, c_518])).
% 2.53/1.40  tff(c_523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_521])).
% 2.53/1.40  tff(c_524, plain, (![A_71]: (~v1_xboole_0(A_71))), inference(splitRight, [status(thm)], [c_122])).
% 2.53/1.40  tff(c_526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_524, c_38])).
% 2.53/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.40  
% 2.53/1.40  Inference rules
% 2.53/1.40  ----------------------
% 2.53/1.40  #Ref     : 0
% 2.53/1.40  #Sup     : 106
% 2.53/1.40  #Fact    : 0
% 2.53/1.40  #Define  : 0
% 2.53/1.40  #Split   : 2
% 2.53/1.40  #Chain   : 0
% 2.53/1.40  #Close   : 0
% 2.53/1.40  
% 2.53/1.40  Ordering : KBO
% 2.53/1.40  
% 2.53/1.40  Simplification rules
% 2.53/1.40  ----------------------
% 2.53/1.40  #Subsume      : 15
% 2.53/1.40  #Demod        : 71
% 2.53/1.40  #Tautology    : 36
% 2.53/1.40  #SimpNegUnit  : 9
% 2.53/1.40  #BackRed      : 6
% 2.53/1.40  
% 2.53/1.40  #Partial instantiations: 0
% 2.53/1.40  #Strategies tried      : 1
% 2.53/1.40  
% 2.53/1.40  Timing (in seconds)
% 2.53/1.40  ----------------------
% 2.53/1.40  Preprocessing        : 0.32
% 2.53/1.40  Parsing              : 0.17
% 2.53/1.40  CNF conversion       : 0.02
% 2.53/1.40  Main loop            : 0.32
% 2.53/1.40  Inferencing          : 0.12
% 2.53/1.40  Reduction            : 0.09
% 2.53/1.40  Demodulation         : 0.06
% 2.53/1.40  BG Simplification    : 0.02
% 2.53/1.40  Subsumption          : 0.06
% 2.53/1.40  Abstraction          : 0.02
% 2.53/1.40  MUC search           : 0.00
% 2.53/1.40  Cooper               : 0.00
% 2.53/1.40  Total                : 0.67
% 2.53/1.40  Index Insertion      : 0.00
% 2.53/1.40  Index Deletion       : 0.00
% 2.53/1.40  Index Matching       : 0.00
% 2.53/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
