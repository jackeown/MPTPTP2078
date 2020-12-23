%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:24 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 191 expanded)
%              Number of leaves         :   34 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  138 ( 439 expanded)
%              Number of equality atoms :   23 (  74 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_99,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_51,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_46,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_60,plain,(
    ! [A_53] :
      ( k1_xboole_0 = A_53
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_69,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_60])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_102,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(A_66,B_67) = '#skF_5'
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_18])).

tff(c_115,plain,(
    ! [B_68] : k4_xboole_0(B_68,B_68) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_14,c_102])).

tff(c_20,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_120,plain,(
    ! [B_68] : r1_tarski('#skF_5',B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_20])).

tff(c_26,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_77,plain,(
    ! [A_16] : m1_subset_1('#skF_5',k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_26])).

tff(c_372,plain,(
    ! [A_100,B_101] :
      ( r1_tarski('#skF_3'(A_100,B_101),B_101)
      | v2_tex_2(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_383,plain,(
    ! [A_102] :
      ( r1_tarski('#skF_3'(A_102,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_102)
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_77,c_372])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_391,plain,(
    ! [A_102] :
      ( '#skF_3'(A_102,'#skF_5') = '#skF_5'
      | ~ r1_tarski('#skF_5','#skF_3'(A_102,'#skF_5'))
      | v2_tex_2('#skF_5',A_102)
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_383,c_10])).

tff(c_403,plain,(
    ! [A_103] :
      ( '#skF_3'(A_103,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_391])).

tff(c_406,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_403,c_46])).

tff(c_409,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_406])).

tff(c_54,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_420,plain,(
    ! [A_104,B_105] :
      ( m1_subset_1('#skF_3'(A_104,B_105),k1_zfmisc_1(u1_struct_0(A_104)))
      | v2_tex_2(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    ! [B_24,A_22] :
      ( v3_pre_topc(B_24,A_22)
      | ~ v1_xboole_0(B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_753,plain,(
    ! [A_138,B_139] :
      ( v3_pre_topc('#skF_3'(A_138,B_139),A_138)
      | ~ v1_xboole_0('#skF_3'(A_138,B_139))
      | ~ v2_pre_topc(A_138)
      | v2_tex_2(B_139,A_138)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(resolution,[status(thm)],[c_420,c_32])).

tff(c_785,plain,(
    ! [A_142] :
      ( v3_pre_topc('#skF_3'(A_142,'#skF_5'),A_142)
      | ~ v1_xboole_0('#skF_3'(A_142,'#skF_5'))
      | ~ v2_pre_topc(A_142)
      | v2_tex_2('#skF_5',A_142)
      | ~ l1_pre_topc(A_142) ) ),
    inference(resolution,[status(thm)],[c_77,c_753])).

tff(c_788,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_4')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_785])).

tff(c_790,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_50,c_409,c_788])).

tff(c_791,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_790])).

tff(c_22,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(A_61,B_62)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_97,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_93])).

tff(c_192,plain,(
    ! [A_75,B_76,C_77] :
      ( k9_subset_1(A_75,B_76,B_76) = B_76
      | ~ m1_subset_1(C_77,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_195,plain,(
    ! [A_75,B_76] :
      ( k9_subset_1(A_75,B_76,B_76) = B_76
      | v1_xboole_0(k1_zfmisc_1(A_75)) ) ),
    inference(resolution,[status(thm)],[c_97,c_192])).

tff(c_200,plain,(
    ! [A_75,B_76] : k9_subset_1(A_75,B_76,B_76) = B_76 ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_195])).

tff(c_536,plain,(
    ! [A_118,B_119,D_120] :
      ( k9_subset_1(u1_struct_0(A_118),B_119,D_120) != '#skF_3'(A_118,B_119)
      | ~ v3_pre_topc(D_120,A_118)
      | ~ m1_subset_1(D_120,k1_zfmisc_1(u1_struct_0(A_118)))
      | v2_tex_2(B_119,A_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_792,plain,(
    ! [A_143,B_144] :
      ( '#skF_3'(A_143,B_144) != B_144
      | ~ v3_pre_topc(B_144,A_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | v2_tex_2(B_144,A_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_536])).

tff(c_808,plain,(
    ! [A_143] :
      ( '#skF_3'(A_143,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_143)
      | v2_tex_2('#skF_5',A_143)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(resolution,[status(thm)],[c_77,c_792])).

tff(c_819,plain,(
    ! [A_145] :
      ( '#skF_3'(A_145,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_145)
      | v2_tex_2('#skF_5',A_145)
      | ~ l1_pre_topc(A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_808])).

tff(c_822,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_791,c_819])).

tff(c_828,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_409,c_822])).

tff(c_830,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_828])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:14:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.61  
% 3.06/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.61  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 3.06/1.61  
% 3.06/1.61  %Foreground sorts:
% 3.06/1.61  
% 3.06/1.61  
% 3.06/1.61  %Background operators:
% 3.06/1.61  
% 3.06/1.61  
% 3.06/1.61  %Foreground operators:
% 3.06/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.06/1.61  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.06/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.06/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.06/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.06/1.61  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.06/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.06/1.61  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.06/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.06/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.06/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.06/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.06/1.61  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.06/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.61  
% 3.06/1.63  tff(f_114, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 3.06/1.63  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.06/1.63  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.06/1.63  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.06/1.63  tff(f_48, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.06/1.63  tff(f_57, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.06/1.63  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 3.06/1.63  tff(f_78, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 3.06/1.63  tff(f_51, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.06/1.63  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.06/1.63  tff(f_61, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.06/1.63  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 3.06/1.63  tff(c_46, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.06/1.63  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.06/1.63  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.06/1.63  tff(c_50, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.06/1.63  tff(c_60, plain, (![A_53]: (k1_xboole_0=A_53 | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.06/1.63  tff(c_69, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_60])).
% 3.06/1.63  tff(c_18, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=k1_xboole_0 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.06/1.63  tff(c_102, plain, (![A_66, B_67]: (k4_xboole_0(A_66, B_67)='#skF_5' | ~r1_tarski(A_66, B_67))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_18])).
% 3.06/1.63  tff(c_115, plain, (![B_68]: (k4_xboole_0(B_68, B_68)='#skF_5')), inference(resolution, [status(thm)], [c_14, c_102])).
% 3.06/1.63  tff(c_20, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.06/1.63  tff(c_120, plain, (![B_68]: (r1_tarski('#skF_5', B_68))), inference(superposition, [status(thm), theory('equality')], [c_115, c_20])).
% 3.06/1.63  tff(c_26, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.06/1.63  tff(c_77, plain, (![A_16]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_26])).
% 3.06/1.63  tff(c_372, plain, (![A_100, B_101]: (r1_tarski('#skF_3'(A_100, B_101), B_101) | v2_tex_2(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.06/1.63  tff(c_383, plain, (![A_102]: (r1_tarski('#skF_3'(A_102, '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', A_102) | ~l1_pre_topc(A_102))), inference(resolution, [status(thm)], [c_77, c_372])).
% 3.06/1.63  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.06/1.63  tff(c_391, plain, (![A_102]: ('#skF_3'(A_102, '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', '#skF_3'(A_102, '#skF_5')) | v2_tex_2('#skF_5', A_102) | ~l1_pre_topc(A_102))), inference(resolution, [status(thm)], [c_383, c_10])).
% 3.06/1.63  tff(c_403, plain, (![A_103]: ('#skF_3'(A_103, '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_103) | ~l1_pre_topc(A_103))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_391])).
% 3.06/1.63  tff(c_406, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_403, c_46])).
% 3.06/1.63  tff(c_409, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_406])).
% 3.06/1.63  tff(c_54, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.06/1.63  tff(c_420, plain, (![A_104, B_105]: (m1_subset_1('#skF_3'(A_104, B_105), k1_zfmisc_1(u1_struct_0(A_104))) | v2_tex_2(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.06/1.63  tff(c_32, plain, (![B_24, A_22]: (v3_pre_topc(B_24, A_22) | ~v1_xboole_0(B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.06/1.63  tff(c_753, plain, (![A_138, B_139]: (v3_pre_topc('#skF_3'(A_138, B_139), A_138) | ~v1_xboole_0('#skF_3'(A_138, B_139)) | ~v2_pre_topc(A_138) | v2_tex_2(B_139, A_138) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(resolution, [status(thm)], [c_420, c_32])).
% 3.06/1.63  tff(c_785, plain, (![A_142]: (v3_pre_topc('#skF_3'(A_142, '#skF_5'), A_142) | ~v1_xboole_0('#skF_3'(A_142, '#skF_5')) | ~v2_pre_topc(A_142) | v2_tex_2('#skF_5', A_142) | ~l1_pre_topc(A_142))), inference(resolution, [status(thm)], [c_77, c_753])).
% 3.06/1.63  tff(c_788, plain, (v3_pre_topc('#skF_5', '#skF_4') | ~v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_4') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_409, c_785])).
% 3.06/1.63  tff(c_790, plain, (v3_pre_topc('#skF_5', '#skF_4') | v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_50, c_409, c_788])).
% 3.06/1.63  tff(c_791, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_790])).
% 3.06/1.63  tff(c_22, plain, (![A_12]: (~v1_xboole_0(k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.06/1.63  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.63  tff(c_93, plain, (![A_61, B_62]: (m1_subset_1(A_61, B_62) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.06/1.63  tff(c_97, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_93])).
% 3.06/1.63  tff(c_192, plain, (![A_75, B_76, C_77]: (k9_subset_1(A_75, B_76, B_76)=B_76 | ~m1_subset_1(C_77, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.06/1.63  tff(c_195, plain, (![A_75, B_76]: (k9_subset_1(A_75, B_76, B_76)=B_76 | v1_xboole_0(k1_zfmisc_1(A_75)))), inference(resolution, [status(thm)], [c_97, c_192])).
% 3.06/1.63  tff(c_200, plain, (![A_75, B_76]: (k9_subset_1(A_75, B_76, B_76)=B_76)), inference(negUnitSimplification, [status(thm)], [c_22, c_195])).
% 3.06/1.63  tff(c_536, plain, (![A_118, B_119, D_120]: (k9_subset_1(u1_struct_0(A_118), B_119, D_120)!='#skF_3'(A_118, B_119) | ~v3_pre_topc(D_120, A_118) | ~m1_subset_1(D_120, k1_zfmisc_1(u1_struct_0(A_118))) | v2_tex_2(B_119, A_118) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.06/1.63  tff(c_792, plain, (![A_143, B_144]: ('#skF_3'(A_143, B_144)!=B_144 | ~v3_pre_topc(B_144, A_143) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | v2_tex_2(B_144, A_143) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(superposition, [status(thm), theory('equality')], [c_200, c_536])).
% 3.06/1.63  tff(c_808, plain, (![A_143]: ('#skF_3'(A_143, '#skF_5')!='#skF_5' | ~v3_pre_topc('#skF_5', A_143) | v2_tex_2('#skF_5', A_143) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(resolution, [status(thm)], [c_77, c_792])).
% 3.06/1.63  tff(c_819, plain, (![A_145]: ('#skF_3'(A_145, '#skF_5')!='#skF_5' | ~v3_pre_topc('#skF_5', A_145) | v2_tex_2('#skF_5', A_145) | ~l1_pre_topc(A_145))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_808])).
% 3.06/1.63  tff(c_822, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_791, c_819])).
% 3.06/1.63  tff(c_828, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_409, c_822])).
% 3.06/1.63  tff(c_830, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_828])).
% 3.06/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.63  
% 3.06/1.63  Inference rules
% 3.06/1.63  ----------------------
% 3.06/1.63  #Ref     : 0
% 3.06/1.63  #Sup     : 166
% 3.06/1.63  #Fact    : 0
% 3.06/1.63  #Define  : 0
% 3.06/1.63  #Split   : 0
% 3.06/1.63  #Chain   : 0
% 3.06/1.63  #Close   : 0
% 3.06/1.63  
% 3.06/1.63  Ordering : KBO
% 3.06/1.63  
% 3.06/1.63  Simplification rules
% 3.06/1.63  ----------------------
% 3.06/1.63  #Subsume      : 23
% 3.06/1.63  #Demod        : 77
% 3.06/1.63  #Tautology    : 64
% 3.06/1.63  #SimpNegUnit  : 19
% 3.06/1.63  #BackRed      : 2
% 3.06/1.63  
% 3.06/1.63  #Partial instantiations: 0
% 3.06/1.63  #Strategies tried      : 1
% 3.06/1.63  
% 3.06/1.63  Timing (in seconds)
% 3.06/1.63  ----------------------
% 3.06/1.63  Preprocessing        : 0.42
% 3.06/1.63  Parsing              : 0.26
% 3.06/1.63  CNF conversion       : 0.02
% 3.06/1.63  Main loop            : 0.36
% 3.17/1.63  Inferencing          : 0.13
% 3.17/1.63  Reduction            : 0.10
% 3.17/1.63  Demodulation         : 0.07
% 3.17/1.63  BG Simplification    : 0.02
% 3.17/1.63  Subsumption          : 0.07
% 3.17/1.63  Abstraction          : 0.02
% 3.17/1.63  MUC search           : 0.00
% 3.17/1.63  Cooper               : 0.00
% 3.17/1.63  Total                : 0.81
% 3.17/1.63  Index Insertion      : 0.00
% 3.17/1.63  Index Deletion       : 0.00
% 3.17/1.63  Index Matching       : 0.00
% 3.17/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
