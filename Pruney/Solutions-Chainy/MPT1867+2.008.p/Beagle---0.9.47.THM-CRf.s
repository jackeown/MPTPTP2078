%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:23 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 202 expanded)
%              Number of leaves         :   32 (  85 expanded)
%              Depth                    :   13
%              Number of atoms          :  119 ( 462 expanded)
%              Number of equality atoms :   26 (  87 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_90,axiom,(
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

tff(f_40,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_38,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_59,plain,(
    ! [A_51] :
      ( k1_xboole_0 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_20,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_71,plain,(
    ! [A_16] : m1_subset_1('#skF_4',k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_20])).

tff(c_529,plain,(
    ! [A_95,B_96] :
      ( r1_tarski('#skF_2'(A_95,B_96),B_96)
      | v2_tex_2(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_534,plain,(
    ! [A_97] :
      ( r1_tarski('#skF_2'(A_97,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_71,c_529])).

tff(c_12,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_95,plain,(
    ! [A_7] :
      ( A_7 = '#skF_4'
      | ~ r1_tarski(A_7,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_12])).

tff(c_539,plain,(
    ! [A_98] :
      ( '#skF_2'(A_98,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_534,c_95])).

tff(c_542,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_539,c_38])).

tff(c_545,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_542])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_556,plain,(
    ! [A_99,B_100] :
      ( m1_subset_1('#skF_2'(A_99,B_100),k1_zfmisc_1(u1_struct_0(A_99)))
      | v2_tex_2(B_100,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [B_22,A_20] :
      ( v3_pre_topc(B_22,A_20)
      | ~ v1_xboole_0(B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1873,plain,(
    ! [A_144,B_145] :
      ( v3_pre_topc('#skF_2'(A_144,B_145),A_144)
      | ~ v1_xboole_0('#skF_2'(A_144,B_145))
      | ~ v2_pre_topc(A_144)
      | v2_tex_2(B_145,A_144)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(resolution,[status(thm)],[c_556,c_24])).

tff(c_2360,plain,(
    ! [A_150] :
      ( v3_pre_topc('#skF_2'(A_150,'#skF_4'),A_150)
      | ~ v1_xboole_0('#skF_2'(A_150,'#skF_4'))
      | ~ v2_pre_topc(A_150)
      | v2_tex_2('#skF_4',A_150)
      | ~ l1_pre_topc(A_150) ) ),
    inference(resolution,[status(thm)],[c_71,c_1873])).

tff(c_2363,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_pre_topc('#skF_3')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_2360])).

tff(c_2365,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_42,c_545,c_2363])).

tff(c_2366,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2365])).

tff(c_167,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k4_xboole_0(A_62,B_63)) = k3_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_97,plain,(
    ! [A_56,B_57] : r1_tarski(k4_xboole_0(A_56,B_57),A_56) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_105,plain,(
    ! [B_57] : k4_xboole_0('#skF_4',B_57) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_97,c_95])).

tff(c_200,plain,(
    ! [B_64] : k3_xboole_0('#skF_4',B_64) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_105])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_205,plain,(
    ! [B_64] : k3_xboole_0(B_64,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_2])).

tff(c_283,plain,(
    ! [A_71,B_72,C_73] :
      ( k9_subset_1(A_71,B_72,C_73) = k3_xboole_0(B_72,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_285,plain,(
    ! [A_16,B_72] : k9_subset_1(A_16,B_72,'#skF_4') = k3_xboole_0(B_72,'#skF_4') ),
    inference(resolution,[status(thm)],[c_71,c_283])).

tff(c_287,plain,(
    ! [A_16,B_72] : k9_subset_1(A_16,B_72,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_285])).

tff(c_1228,plain,(
    ! [A_123,B_124,D_125] :
      ( k9_subset_1(u1_struct_0(A_123),B_124,D_125) != '#skF_2'(A_123,B_124)
      | ~ v3_pre_topc(D_125,A_123)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(u1_struct_0(A_123)))
      | v2_tex_2(B_124,A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1234,plain,(
    ! [A_123,B_72] :
      ( '#skF_2'(A_123,B_72) != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_123)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_123)))
      | v2_tex_2(B_72,A_123)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_1228])).

tff(c_2421,plain,(
    ! [A_159,B_160] :
      ( '#skF_2'(A_159,B_160) != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_159)
      | v2_tex_2(B_160,A_159)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_1234])).

tff(c_2435,plain,(
    ! [A_161] :
      ( '#skF_2'(A_161,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_161)
      | v2_tex_2('#skF_4',A_161)
      | ~ l1_pre_topc(A_161) ) ),
    inference(resolution,[status(thm)],[c_71,c_2421])).

tff(c_2438,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2366,c_2435])).

tff(c_2444,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_545,c_2438])).

tff(c_2446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2444])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.02/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/1.77  
% 4.02/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/1.78  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 4.38/1.78  
% 4.38/1.78  %Foreground sorts:
% 4.38/1.78  
% 4.38/1.78  
% 4.38/1.78  %Background operators:
% 4.38/1.78  
% 4.38/1.78  
% 4.38/1.78  %Foreground operators:
% 4.38/1.78  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.38/1.78  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.38/1.78  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.38/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.38/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.38/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.38/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.38/1.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.38/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.38/1.78  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.38/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.38/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.38/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.38/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.38/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.38/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.38/1.78  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.38/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.38/1.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.38/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.38/1.78  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.38/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.38/1.78  
% 4.45/1.79  tff(f_105, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 4.45/1.79  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.45/1.79  tff(f_52, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.45/1.79  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 4.45/1.79  tff(f_40, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.45/1.79  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tops_1)).
% 4.45/1.79  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.45/1.79  tff(f_34, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.45/1.79  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.45/1.79  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.45/1.79  tff(c_38, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.45/1.79  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.45/1.79  tff(c_42, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.45/1.79  tff(c_59, plain, (![A_51]: (k1_xboole_0=A_51 | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.45/1.79  tff(c_68, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_42, c_59])).
% 4.45/1.79  tff(c_20, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.45/1.79  tff(c_71, plain, (![A_16]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_20])).
% 4.45/1.79  tff(c_529, plain, (![A_95, B_96]: (r1_tarski('#skF_2'(A_95, B_96), B_96) | v2_tex_2(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.45/1.79  tff(c_534, plain, (![A_97]: (r1_tarski('#skF_2'(A_97, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_97) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_71, c_529])).
% 4.45/1.79  tff(c_12, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.45/1.79  tff(c_95, plain, (![A_7]: (A_7='#skF_4' | ~r1_tarski(A_7, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_12])).
% 4.45/1.79  tff(c_539, plain, (![A_98]: ('#skF_2'(A_98, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_98) | ~l1_pre_topc(A_98))), inference(resolution, [status(thm)], [c_534, c_95])).
% 4.45/1.79  tff(c_542, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_539, c_38])).
% 4.45/1.79  tff(c_545, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_542])).
% 4.45/1.79  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.45/1.79  tff(c_556, plain, (![A_99, B_100]: (m1_subset_1('#skF_2'(A_99, B_100), k1_zfmisc_1(u1_struct_0(A_99))) | v2_tex_2(B_100, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.45/1.79  tff(c_24, plain, (![B_22, A_20]: (v3_pre_topc(B_22, A_20) | ~v1_xboole_0(B_22) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.45/1.79  tff(c_1873, plain, (![A_144, B_145]: (v3_pre_topc('#skF_2'(A_144, B_145), A_144) | ~v1_xboole_0('#skF_2'(A_144, B_145)) | ~v2_pre_topc(A_144) | v2_tex_2(B_145, A_144) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(resolution, [status(thm)], [c_556, c_24])).
% 4.45/1.79  tff(c_2360, plain, (![A_150]: (v3_pre_topc('#skF_2'(A_150, '#skF_4'), A_150) | ~v1_xboole_0('#skF_2'(A_150, '#skF_4')) | ~v2_pre_topc(A_150) | v2_tex_2('#skF_4', A_150) | ~l1_pre_topc(A_150))), inference(resolution, [status(thm)], [c_71, c_1873])).
% 4.45/1.79  tff(c_2363, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_pre_topc('#skF_3') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_545, c_2360])).
% 4.45/1.79  tff(c_2365, plain, (v3_pre_topc('#skF_4', '#skF_3') | v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_42, c_545, c_2363])).
% 4.45/1.79  tff(c_2366, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_2365])).
% 4.45/1.79  tff(c_167, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k4_xboole_0(A_62, B_63))=k3_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.45/1.79  tff(c_97, plain, (![A_56, B_57]: (r1_tarski(k4_xboole_0(A_56, B_57), A_56))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.45/1.79  tff(c_105, plain, (![B_57]: (k4_xboole_0('#skF_4', B_57)='#skF_4')), inference(resolution, [status(thm)], [c_97, c_95])).
% 4.45/1.79  tff(c_200, plain, (![B_64]: (k3_xboole_0('#skF_4', B_64)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_167, c_105])).
% 4.45/1.79  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.45/1.79  tff(c_205, plain, (![B_64]: (k3_xboole_0(B_64, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_200, c_2])).
% 4.45/1.79  tff(c_283, plain, (![A_71, B_72, C_73]: (k9_subset_1(A_71, B_72, C_73)=k3_xboole_0(B_72, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.45/1.79  tff(c_285, plain, (![A_16, B_72]: (k9_subset_1(A_16, B_72, '#skF_4')=k3_xboole_0(B_72, '#skF_4'))), inference(resolution, [status(thm)], [c_71, c_283])).
% 4.45/1.79  tff(c_287, plain, (![A_16, B_72]: (k9_subset_1(A_16, B_72, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_285])).
% 4.45/1.79  tff(c_1228, plain, (![A_123, B_124, D_125]: (k9_subset_1(u1_struct_0(A_123), B_124, D_125)!='#skF_2'(A_123, B_124) | ~v3_pre_topc(D_125, A_123) | ~m1_subset_1(D_125, k1_zfmisc_1(u1_struct_0(A_123))) | v2_tex_2(B_124, A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.45/1.79  tff(c_1234, plain, (![A_123, B_72]: ('#skF_2'(A_123, B_72)!='#skF_4' | ~v3_pre_topc('#skF_4', A_123) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_123))) | v2_tex_2(B_72, A_123) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123))), inference(superposition, [status(thm), theory('equality')], [c_287, c_1228])).
% 4.45/1.79  tff(c_2421, plain, (![A_159, B_160]: ('#skF_2'(A_159, B_160)!='#skF_4' | ~v3_pre_topc('#skF_4', A_159) | v2_tex_2(B_160, A_159) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_1234])).
% 4.45/1.79  tff(c_2435, plain, (![A_161]: ('#skF_2'(A_161, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_161) | v2_tex_2('#skF_4', A_161) | ~l1_pre_topc(A_161))), inference(resolution, [status(thm)], [c_71, c_2421])).
% 4.45/1.79  tff(c_2438, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2366, c_2435])).
% 4.45/1.79  tff(c_2444, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_545, c_2438])).
% 4.45/1.79  tff(c_2446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_2444])).
% 4.45/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.79  
% 4.45/1.79  Inference rules
% 4.45/1.79  ----------------------
% 4.45/1.79  #Ref     : 0
% 4.45/1.79  #Sup     : 574
% 4.45/1.79  #Fact    : 0
% 4.45/1.79  #Define  : 0
% 4.45/1.79  #Split   : 0
% 4.45/1.79  #Chain   : 0
% 4.45/1.79  #Close   : 0
% 4.45/1.79  
% 4.45/1.79  Ordering : KBO
% 4.45/1.79  
% 4.45/1.79  Simplification rules
% 4.45/1.79  ----------------------
% 4.45/1.79  #Subsume      : 10
% 4.45/1.79  #Demod        : 795
% 4.45/1.79  #Tautology    : 382
% 4.45/1.79  #SimpNegUnit  : 6
% 4.45/1.79  #BackRed      : 4
% 4.45/1.79  
% 4.45/1.79  #Partial instantiations: 0
% 4.45/1.79  #Strategies tried      : 1
% 4.45/1.79  
% 4.45/1.79  Timing (in seconds)
% 4.45/1.79  ----------------------
% 4.45/1.79  Preprocessing        : 0.32
% 4.45/1.79  Parsing              : 0.17
% 4.45/1.79  CNF conversion       : 0.02
% 4.45/1.79  Main loop            : 0.68
% 4.45/1.79  Inferencing          : 0.19
% 4.45/1.79  Reduction            : 0.35
% 4.45/1.79  Demodulation         : 0.31
% 4.45/1.79  BG Simplification    : 0.03
% 4.45/1.79  Subsumption          : 0.08
% 4.45/1.79  Abstraction          : 0.03
% 4.45/1.79  MUC search           : 0.00
% 4.45/1.80  Cooper               : 0.00
% 4.45/1.80  Total                : 1.04
% 4.45/1.80  Index Insertion      : 0.00
% 4.45/1.80  Index Deletion       : 0.00
% 4.45/1.80  Index Matching       : 0.00
% 4.45/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
