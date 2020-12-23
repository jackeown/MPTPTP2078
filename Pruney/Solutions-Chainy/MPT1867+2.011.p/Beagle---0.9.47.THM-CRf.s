%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:23 EST 2020

% Result     : Theorem 7.34s
% Output     : CNFRefutation 7.34s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 181 expanded)
%              Number of leaves         :   32 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :  137 ( 426 expanded)
%              Number of equality atoms :   19 (  59 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_63,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_57,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_48,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_52,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_62,plain,(
    ! [A_51] :
      ( k1_xboole_0 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_52,c_62])).

tff(c_26,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_72,plain,(
    ! [A_14] : m1_subset_1('#skF_5',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_26])).

tff(c_87,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_91,plain,(
    ! [A_14] : r1_tarski('#skF_5',A_14) ),
    inference(resolution,[status(thm)],[c_72,c_87])).

tff(c_340,plain,(
    ! [A_96,B_97] :
      ( r1_tarski('#skF_3'(A_96,B_97),B_97)
      | v2_tex_2(B_97,A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_375,plain,(
    ! [A_99] :
      ( r1_tarski('#skF_3'(A_99,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_72,c_340])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_380,plain,(
    ! [A_99] :
      ( '#skF_3'(A_99,'#skF_5') = '#skF_5'
      | ~ r1_tarski('#skF_5','#skF_3'(A_99,'#skF_5'))
      | v2_tex_2('#skF_5',A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_375,c_8])).

tff(c_385,plain,(
    ! [A_100] :
      ( '#skF_3'(A_100,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_380])).

tff(c_388,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_385,c_48])).

tff(c_391,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_388])).

tff(c_56,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_402,plain,(
    ! [A_101,B_102] :
      ( m1_subset_1('#skF_3'(A_101,B_102),k1_zfmisc_1(u1_struct_0(A_101)))
      | v2_tex_2(B_102,A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34,plain,(
    ! [B_22,A_20] :
      ( v3_pre_topc(B_22,A_20)
      | ~ v1_xboole_0(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1739,plain,(
    ! [A_175,B_176] :
      ( v3_pre_topc('#skF_3'(A_175,B_176),A_175)
      | ~ v1_xboole_0('#skF_3'(A_175,B_176))
      | ~ v2_pre_topc(A_175)
      | v2_tex_2(B_176,A_175)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175) ) ),
    inference(resolution,[status(thm)],[c_402,c_34])).

tff(c_1829,plain,(
    ! [A_184] :
      ( v3_pre_topc('#skF_3'(A_184,'#skF_5'),A_184)
      | ~ v1_xboole_0('#skF_3'(A_184,'#skF_5'))
      | ~ v2_pre_topc(A_184)
      | v2_tex_2('#skF_5',A_184)
      | ~ l1_pre_topc(A_184) ) ),
    inference(resolution,[status(thm)],[c_72,c_1739])).

tff(c_1832,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_4')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_1829])).

tff(c_1834,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_52,c_391,c_1832])).

tff(c_1835,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1834])).

tff(c_22,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [B_66,A_67] :
      ( m1_subset_1(B_66,A_67)
      | ~ r2_hidden(B_66,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_122,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_118])).

tff(c_176,plain,(
    ! [A_75,B_76,C_77] :
      ( k9_subset_1(A_75,B_76,B_76) = B_76
      | ~ m1_subset_1(C_77,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_179,plain,(
    ! [A_75,B_76] :
      ( k9_subset_1(A_75,B_76,B_76) = B_76
      | v1_xboole_0(k1_zfmisc_1(A_75)) ) ),
    inference(resolution,[status(thm)],[c_122,c_176])).

tff(c_189,plain,(
    ! [A_75,B_76] : k9_subset_1(A_75,B_76,B_76) = B_76 ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_179])).

tff(c_576,plain,(
    ! [A_116,B_117,D_118] :
      ( k9_subset_1(u1_struct_0(A_116),B_117,D_118) != '#skF_3'(A_116,B_117)
      | ~ v3_pre_topc(D_118,A_116)
      | ~ m1_subset_1(D_118,k1_zfmisc_1(u1_struct_0(A_116)))
      | v2_tex_2(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6597,plain,(
    ! [A_351,B_352] :
      ( '#skF_3'(A_351,B_352) != B_352
      | ~ v3_pre_topc(B_352,A_351)
      | ~ m1_subset_1(B_352,k1_zfmisc_1(u1_struct_0(A_351)))
      | v2_tex_2(B_352,A_351)
      | ~ m1_subset_1(B_352,k1_zfmisc_1(u1_struct_0(A_351)))
      | ~ l1_pre_topc(A_351) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_576])).

tff(c_6637,plain,(
    ! [A_351] :
      ( '#skF_3'(A_351,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_351)
      | v2_tex_2('#skF_5',A_351)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_351)))
      | ~ l1_pre_topc(A_351) ) ),
    inference(resolution,[status(thm)],[c_72,c_6597])).

tff(c_6656,plain,(
    ! [A_353] :
      ( '#skF_3'(A_353,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_353)
      | v2_tex_2('#skF_5',A_353)
      | ~ l1_pre_topc(A_353) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6637])).

tff(c_6659,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1835,c_6656])).

tff(c_6665,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_391,c_6659])).

tff(c_6667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_6665])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:06:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.34/2.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.34/2.57  
% 7.34/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.34/2.57  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 7.34/2.57  
% 7.34/2.57  %Foreground sorts:
% 7.34/2.57  
% 7.34/2.57  
% 7.34/2.57  %Background operators:
% 7.34/2.57  
% 7.34/2.57  
% 7.34/2.57  %Foreground operators:
% 7.34/2.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.34/2.57  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.34/2.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.34/2.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.34/2.57  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.34/2.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.34/2.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.34/2.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.34/2.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.34/2.57  tff('#skF_5', type, '#skF_5': $i).
% 7.34/2.57  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 7.34/2.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.34/2.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.34/2.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.34/2.57  tff('#skF_4', type, '#skF_4': $i).
% 7.34/2.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.34/2.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.34/2.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.34/2.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.34/2.57  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.34/2.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.34/2.57  
% 7.34/2.59  tff(f_120, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 7.34/2.59  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.34/2.59  tff(f_63, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 7.34/2.59  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.34/2.59  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 7.34/2.59  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.34/2.59  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tops_1)).
% 7.34/2.59  tff(f_57, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 7.34/2.59  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.34/2.59  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 7.34/2.59  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 7.34/2.59  tff(c_48, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.34/2.59  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.34/2.59  tff(c_52, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.34/2.59  tff(c_62, plain, (![A_51]: (k1_xboole_0=A_51 | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.34/2.59  tff(c_66, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_52, c_62])).
% 7.34/2.59  tff(c_26, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.34/2.59  tff(c_72, plain, (![A_14]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_26])).
% 7.34/2.59  tff(c_87, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.34/2.59  tff(c_91, plain, (![A_14]: (r1_tarski('#skF_5', A_14))), inference(resolution, [status(thm)], [c_72, c_87])).
% 7.34/2.59  tff(c_340, plain, (![A_96, B_97]: (r1_tarski('#skF_3'(A_96, B_97), B_97) | v2_tex_2(B_97, A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.34/2.59  tff(c_375, plain, (![A_99]: (r1_tarski('#skF_3'(A_99, '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', A_99) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_72, c_340])).
% 7.34/2.59  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.34/2.59  tff(c_380, plain, (![A_99]: ('#skF_3'(A_99, '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', '#skF_3'(A_99, '#skF_5')) | v2_tex_2('#skF_5', A_99) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_375, c_8])).
% 7.34/2.59  tff(c_385, plain, (![A_100]: ('#skF_3'(A_100, '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_100) | ~l1_pre_topc(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_380])).
% 7.34/2.59  tff(c_388, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_385, c_48])).
% 7.34/2.59  tff(c_391, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_388])).
% 7.34/2.59  tff(c_56, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.34/2.59  tff(c_402, plain, (![A_101, B_102]: (m1_subset_1('#skF_3'(A_101, B_102), k1_zfmisc_1(u1_struct_0(A_101))) | v2_tex_2(B_102, A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.34/2.59  tff(c_34, plain, (![B_22, A_20]: (v3_pre_topc(B_22, A_20) | ~v1_xboole_0(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.34/2.59  tff(c_1739, plain, (![A_175, B_176]: (v3_pre_topc('#skF_3'(A_175, B_176), A_175) | ~v1_xboole_0('#skF_3'(A_175, B_176)) | ~v2_pre_topc(A_175) | v2_tex_2(B_176, A_175) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175))), inference(resolution, [status(thm)], [c_402, c_34])).
% 7.34/2.59  tff(c_1829, plain, (![A_184]: (v3_pre_topc('#skF_3'(A_184, '#skF_5'), A_184) | ~v1_xboole_0('#skF_3'(A_184, '#skF_5')) | ~v2_pre_topc(A_184) | v2_tex_2('#skF_5', A_184) | ~l1_pre_topc(A_184))), inference(resolution, [status(thm)], [c_72, c_1739])).
% 7.34/2.59  tff(c_1832, plain, (v3_pre_topc('#skF_5', '#skF_4') | ~v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_4') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_391, c_1829])).
% 7.34/2.59  tff(c_1834, plain, (v3_pre_topc('#skF_5', '#skF_4') | v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_52, c_391, c_1832])).
% 7.34/2.59  tff(c_1835, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_48, c_1834])).
% 7.34/2.59  tff(c_22, plain, (![A_10]: (~v1_xboole_0(k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.34/2.59  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.34/2.59  tff(c_118, plain, (![B_66, A_67]: (m1_subset_1(B_66, A_67) | ~r2_hidden(B_66, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.34/2.59  tff(c_122, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_118])).
% 7.34/2.59  tff(c_176, plain, (![A_75, B_76, C_77]: (k9_subset_1(A_75, B_76, B_76)=B_76 | ~m1_subset_1(C_77, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.34/2.59  tff(c_179, plain, (![A_75, B_76]: (k9_subset_1(A_75, B_76, B_76)=B_76 | v1_xboole_0(k1_zfmisc_1(A_75)))), inference(resolution, [status(thm)], [c_122, c_176])).
% 7.34/2.59  tff(c_189, plain, (![A_75, B_76]: (k9_subset_1(A_75, B_76, B_76)=B_76)), inference(negUnitSimplification, [status(thm)], [c_22, c_179])).
% 7.34/2.59  tff(c_576, plain, (![A_116, B_117, D_118]: (k9_subset_1(u1_struct_0(A_116), B_117, D_118)!='#skF_3'(A_116, B_117) | ~v3_pre_topc(D_118, A_116) | ~m1_subset_1(D_118, k1_zfmisc_1(u1_struct_0(A_116))) | v2_tex_2(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.34/2.59  tff(c_6597, plain, (![A_351, B_352]: ('#skF_3'(A_351, B_352)!=B_352 | ~v3_pre_topc(B_352, A_351) | ~m1_subset_1(B_352, k1_zfmisc_1(u1_struct_0(A_351))) | v2_tex_2(B_352, A_351) | ~m1_subset_1(B_352, k1_zfmisc_1(u1_struct_0(A_351))) | ~l1_pre_topc(A_351))), inference(superposition, [status(thm), theory('equality')], [c_189, c_576])).
% 7.34/2.59  tff(c_6637, plain, (![A_351]: ('#skF_3'(A_351, '#skF_5')!='#skF_5' | ~v3_pre_topc('#skF_5', A_351) | v2_tex_2('#skF_5', A_351) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_351))) | ~l1_pre_topc(A_351))), inference(resolution, [status(thm)], [c_72, c_6597])).
% 7.34/2.59  tff(c_6656, plain, (![A_353]: ('#skF_3'(A_353, '#skF_5')!='#skF_5' | ~v3_pre_topc('#skF_5', A_353) | v2_tex_2('#skF_5', A_353) | ~l1_pre_topc(A_353))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6637])).
% 7.34/2.59  tff(c_6659, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1835, c_6656])).
% 7.34/2.59  tff(c_6665, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_391, c_6659])).
% 7.34/2.59  tff(c_6667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_6665])).
% 7.34/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.34/2.59  
% 7.34/2.59  Inference rules
% 7.34/2.59  ----------------------
% 7.34/2.59  #Ref     : 0
% 7.34/2.59  #Sup     : 1528
% 7.34/2.59  #Fact    : 0
% 7.34/2.59  #Define  : 0
% 7.34/2.59  #Split   : 7
% 7.34/2.59  #Chain   : 0
% 7.34/2.59  #Close   : 0
% 7.34/2.59  
% 7.34/2.59  Ordering : KBO
% 7.34/2.59  
% 7.34/2.59  Simplification rules
% 7.34/2.59  ----------------------
% 7.34/2.59  #Subsume      : 544
% 7.34/2.59  #Demod        : 1463
% 7.34/2.59  #Tautology    : 357
% 7.34/2.59  #SimpNegUnit  : 304
% 7.34/2.59  #BackRed      : 5
% 7.34/2.59  
% 7.34/2.59  #Partial instantiations: 0
% 7.34/2.59  #Strategies tried      : 1
% 7.34/2.59  
% 7.34/2.59  Timing (in seconds)
% 7.34/2.59  ----------------------
% 7.34/2.59  Preprocessing        : 0.31
% 7.34/2.59  Parsing              : 0.17
% 7.34/2.59  CNF conversion       : 0.03
% 7.34/2.59  Main loop            : 1.51
% 7.34/2.59  Inferencing          : 0.43
% 7.34/2.59  Reduction            : 0.44
% 7.34/2.59  Demodulation         : 0.29
% 7.34/2.59  BG Simplification    : 0.06
% 7.34/2.59  Subsumption          : 0.48
% 7.34/2.59  Abstraction          : 0.07
% 7.34/2.59  MUC search           : 0.00
% 7.34/2.59  Cooper               : 0.00
% 7.34/2.59  Total                : 1.85
% 7.34/2.59  Index Insertion      : 0.00
% 7.34/2.59  Index Deletion       : 0.00
% 7.34/2.59  Index Matching       : 0.00
% 7.34/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
