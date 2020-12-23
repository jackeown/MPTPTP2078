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
% DateTime   : Thu Dec  3 10:29:24 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 201 expanded)
%              Number of leaves         :   29 (  82 expanded)
%              Depth                    :   15
%              Number of atoms          :  126 ( 481 expanded)
%              Number of equality atoms :   19 (  67 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_51,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_87,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_42,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_36,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_42,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_14,plain,(
    ! [A_10] : v1_xboole_0('#skF_2'(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_40,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_52,plain,(
    ! [B_47,A_48] :
      ( ~ v1_xboole_0(B_47)
      | B_47 = A_48
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    ! [A_49] :
      ( A_49 = '#skF_6'
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_40,c_52])).

tff(c_66,plain,(
    ! [A_10] : '#skF_2'(A_10) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_14,c_59])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1('#skF_2'(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_69,plain,(
    ! [A_10] : m1_subset_1('#skF_6',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_16])).

tff(c_82,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    ! [A_10] : r1_tarski('#skF_6',A_10) ),
    inference(resolution,[status(thm)],[c_69,c_82])).

tff(c_195,plain,(
    ! [A_70,B_71] :
      ( r1_tarski('#skF_4'(A_70,B_71),B_71)
      | v2_tex_2(B_71,A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_208,plain,(
    ! [A_72] :
      ( r1_tarski('#skF_4'(A_72,'#skF_6'),'#skF_6')
      | v2_tex_2('#skF_6',A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_69,c_195])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_213,plain,(
    ! [A_72] :
      ( '#skF_4'(A_72,'#skF_6') = '#skF_6'
      | ~ r1_tarski('#skF_6','#skF_4'(A_72,'#skF_6'))
      | v2_tex_2('#skF_6',A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_208,c_2])).

tff(c_218,plain,(
    ! [A_73] :
      ( '#skF_4'(A_73,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_213])).

tff(c_221,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_218,c_36])).

tff(c_224,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_221])).

tff(c_44,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_253,plain,(
    ! [A_76,B_77] :
      ( m1_subset_1('#skF_4'(A_76,B_77),k1_zfmisc_1(u1_struct_0(A_76)))
      | v2_tex_2(B_77,A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    ! [B_16,A_14] :
      ( v3_pre_topc(B_16,A_14)
      | ~ v1_xboole_0(B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_384,plain,(
    ! [A_102,B_103] :
      ( v3_pre_topc('#skF_4'(A_102,B_103),A_102)
      | ~ v1_xboole_0('#skF_4'(A_102,B_103))
      | ~ v2_pre_topc(A_102)
      | v2_tex_2(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_253,c_22])).

tff(c_403,plain,(
    ! [A_104] :
      ( v3_pre_topc('#skF_4'(A_104,'#skF_6'),A_104)
      | ~ v1_xboole_0('#skF_4'(A_104,'#skF_6'))
      | ~ v2_pre_topc(A_104)
      | v2_tex_2('#skF_6',A_104)
      | ~ l1_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_69,c_384])).

tff(c_406,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | ~ v1_xboole_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_pre_topc('#skF_5')
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_403])).

tff(c_408,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_40,c_224,c_406])).

tff(c_409,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_408])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1('#skF_1'(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_142,plain,(
    ! [A_61,B_62,C_63] :
      ( k9_subset_1(A_61,B_62,B_62) = B_62
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_151,plain,(
    ! [A_61,B_62] : k9_subset_1(A_61,B_62,B_62) = B_62 ),
    inference(resolution,[status(thm)],[c_10,c_142])).

tff(c_380,plain,(
    ! [A_99,B_100,D_101] :
      ( k9_subset_1(u1_struct_0(A_99),B_100,D_101) != '#skF_4'(A_99,B_100)
      | ~ v3_pre_topc(D_101,A_99)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(u1_struct_0(A_99)))
      | v2_tex_2(B_100,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_501,plain,(
    ! [A_117,B_118] :
      ( '#skF_4'(A_117,B_118) != B_118
      | ~ v3_pre_topc(B_118,A_117)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | v2_tex_2(B_118,A_117)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_380])).

tff(c_511,plain,(
    ! [A_117] :
      ( '#skF_4'(A_117,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_117)
      | v2_tex_2('#skF_6',A_117)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(resolution,[status(thm)],[c_69,c_501])).

tff(c_524,plain,(
    ! [A_119] :
      ( '#skF_4'(A_119,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_119)
      | v2_tex_2('#skF_6',A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_511])).

tff(c_527,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_409,c_524])).

tff(c_533,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_224,c_527])).

tff(c_535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_533])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.36  
% 2.52/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.36  %$ v3_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.82/1.36  
% 2.82/1.36  %Foreground sorts:
% 2.82/1.36  
% 2.82/1.36  
% 2.82/1.36  %Background operators:
% 2.82/1.36  
% 2.82/1.36  
% 2.82/1.36  %Foreground operators:
% 2.82/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.82/1.36  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.82/1.36  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.82/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.82/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.82/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.36  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.82/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.82/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.82/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.82/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.82/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.82/1.36  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.82/1.36  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.82/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.36  
% 2.82/1.38  tff(f_102, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.82/1.38  tff(f_51, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 2.82/1.38  tff(f_39, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.82/1.38  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.82/1.38  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 2.82/1.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.82/1.38  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 2.82/1.38  tff(f_42, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.82/1.38  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 2.82/1.38  tff(c_36, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.82/1.38  tff(c_42, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.82/1.38  tff(c_14, plain, (![A_10]: (v1_xboole_0('#skF_2'(A_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.82/1.38  tff(c_40, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.82/1.38  tff(c_52, plain, (![B_47, A_48]: (~v1_xboole_0(B_47) | B_47=A_48 | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.82/1.38  tff(c_59, plain, (![A_49]: (A_49='#skF_6' | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_40, c_52])).
% 2.82/1.38  tff(c_66, plain, (![A_10]: ('#skF_2'(A_10)='#skF_6')), inference(resolution, [status(thm)], [c_14, c_59])).
% 2.82/1.38  tff(c_16, plain, (![A_10]: (m1_subset_1('#skF_2'(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.82/1.38  tff(c_69, plain, (![A_10]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_16])).
% 2.82/1.38  tff(c_82, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.82/1.38  tff(c_90, plain, (![A_10]: (r1_tarski('#skF_6', A_10))), inference(resolution, [status(thm)], [c_69, c_82])).
% 2.82/1.38  tff(c_195, plain, (![A_70, B_71]: (r1_tarski('#skF_4'(A_70, B_71), B_71) | v2_tex_2(B_71, A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.82/1.38  tff(c_208, plain, (![A_72]: (r1_tarski('#skF_4'(A_72, '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', A_72) | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_69, c_195])).
% 2.82/1.38  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.38  tff(c_213, plain, (![A_72]: ('#skF_4'(A_72, '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', '#skF_4'(A_72, '#skF_6')) | v2_tex_2('#skF_6', A_72) | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_208, c_2])).
% 2.82/1.38  tff(c_218, plain, (![A_73]: ('#skF_4'(A_73, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_73) | ~l1_pre_topc(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_213])).
% 2.82/1.38  tff(c_221, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_218, c_36])).
% 2.82/1.38  tff(c_224, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_221])).
% 2.82/1.38  tff(c_44, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.82/1.38  tff(c_253, plain, (![A_76, B_77]: (m1_subset_1('#skF_4'(A_76, B_77), k1_zfmisc_1(u1_struct_0(A_76))) | v2_tex_2(B_77, A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.82/1.38  tff(c_22, plain, (![B_16, A_14]: (v3_pre_topc(B_16, A_14) | ~v1_xboole_0(B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.82/1.38  tff(c_384, plain, (![A_102, B_103]: (v3_pre_topc('#skF_4'(A_102, B_103), A_102) | ~v1_xboole_0('#skF_4'(A_102, B_103)) | ~v2_pre_topc(A_102) | v2_tex_2(B_103, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(resolution, [status(thm)], [c_253, c_22])).
% 2.82/1.38  tff(c_403, plain, (![A_104]: (v3_pre_topc('#skF_4'(A_104, '#skF_6'), A_104) | ~v1_xboole_0('#skF_4'(A_104, '#skF_6')) | ~v2_pre_topc(A_104) | v2_tex_2('#skF_6', A_104) | ~l1_pre_topc(A_104))), inference(resolution, [status(thm)], [c_69, c_384])).
% 2.82/1.38  tff(c_406, plain, (v3_pre_topc('#skF_6', '#skF_5') | ~v1_xboole_0('#skF_4'('#skF_5', '#skF_6')) | ~v2_pre_topc('#skF_5') | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_224, c_403])).
% 2.82/1.38  tff(c_408, plain, (v3_pre_topc('#skF_6', '#skF_5') | v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_40, c_224, c_406])).
% 2.82/1.38  tff(c_409, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_36, c_408])).
% 2.82/1.38  tff(c_10, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.82/1.38  tff(c_142, plain, (![A_61, B_62, C_63]: (k9_subset_1(A_61, B_62, B_62)=B_62 | ~m1_subset_1(C_63, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.82/1.38  tff(c_151, plain, (![A_61, B_62]: (k9_subset_1(A_61, B_62, B_62)=B_62)), inference(resolution, [status(thm)], [c_10, c_142])).
% 2.82/1.38  tff(c_380, plain, (![A_99, B_100, D_101]: (k9_subset_1(u1_struct_0(A_99), B_100, D_101)!='#skF_4'(A_99, B_100) | ~v3_pre_topc(D_101, A_99) | ~m1_subset_1(D_101, k1_zfmisc_1(u1_struct_0(A_99))) | v2_tex_2(B_100, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.82/1.38  tff(c_501, plain, (![A_117, B_118]: ('#skF_4'(A_117, B_118)!=B_118 | ~v3_pre_topc(B_118, A_117) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | v2_tex_2(B_118, A_117) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(superposition, [status(thm), theory('equality')], [c_151, c_380])).
% 2.82/1.38  tff(c_511, plain, (![A_117]: ('#skF_4'(A_117, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_6', A_117) | v2_tex_2('#skF_6', A_117) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(resolution, [status(thm)], [c_69, c_501])).
% 2.82/1.38  tff(c_524, plain, (![A_119]: ('#skF_4'(A_119, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_6', A_119) | v2_tex_2('#skF_6', A_119) | ~l1_pre_topc(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_511])).
% 2.82/1.38  tff(c_527, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_409, c_524])).
% 2.82/1.38  tff(c_533, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_224, c_527])).
% 2.82/1.38  tff(c_535, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_533])).
% 2.82/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.38  
% 2.82/1.38  Inference rules
% 2.82/1.38  ----------------------
% 2.82/1.38  #Ref     : 0
% 2.82/1.38  #Sup     : 102
% 2.82/1.38  #Fact    : 0
% 2.82/1.38  #Define  : 0
% 2.82/1.38  #Split   : 0
% 2.82/1.38  #Chain   : 0
% 2.82/1.38  #Close   : 0
% 2.82/1.38  
% 2.82/1.38  Ordering : KBO
% 2.82/1.38  
% 2.82/1.38  Simplification rules
% 2.82/1.38  ----------------------
% 2.82/1.38  #Subsume      : 9
% 2.82/1.38  #Demod        : 58
% 2.82/1.38  #Tautology    : 37
% 2.82/1.38  #SimpNegUnit  : 9
% 2.82/1.38  #BackRed      : 2
% 2.82/1.38  
% 2.82/1.38  #Partial instantiations: 0
% 2.82/1.38  #Strategies tried      : 1
% 2.82/1.38  
% 2.82/1.38  Timing (in seconds)
% 2.82/1.38  ----------------------
% 2.82/1.38  Preprocessing        : 0.30
% 2.82/1.38  Parsing              : 0.17
% 2.82/1.38  CNF conversion       : 0.02
% 2.82/1.38  Main loop            : 0.31
% 2.82/1.38  Inferencing          : 0.12
% 2.82/1.38  Reduction            : 0.09
% 2.82/1.38  Demodulation         : 0.06
% 2.82/1.38  BG Simplification    : 0.02
% 2.82/1.38  Subsumption          : 0.06
% 2.82/1.38  Abstraction          : 0.01
% 2.82/1.38  MUC search           : 0.00
% 2.82/1.38  Cooper               : 0.00
% 2.82/1.38  Total                : 0.65
% 2.82/1.38  Index Insertion      : 0.00
% 2.82/1.38  Index Deletion       : 0.00
% 2.82/1.38  Index Matching       : 0.00
% 2.82/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
