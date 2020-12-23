%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:28 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 136 expanded)
%              Number of leaves         :   32 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  114 ( 276 expanded)
%              Number of equality atoms :   31 (  61 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(f_107,negated_conjecture,(
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

tff(f_42,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_92,axiom,(
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
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_65,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_74,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_65])).

tff(c_16,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    ! [A_6] : k4_xboole_0(A_6,'#skF_4') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_16])).

tff(c_24,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_77,plain,(
    ! [A_13] : m1_subset_1('#skF_4',k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_24])).

tff(c_352,plain,(
    ! [A_88,B_89] :
      ( r1_tarski('#skF_2'(A_88,B_89),B_89)
      | v2_tex_2(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_357,plain,(
    ! [A_90] :
      ( r1_tarski('#skF_2'(A_90,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_77,c_352])).

tff(c_14,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = k1_xboole_0
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_109,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = '#skF_4'
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_14])).

tff(c_365,plain,(
    ! [A_90] :
      ( k4_xboole_0('#skF_2'(A_90,'#skF_4'),'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_357,c_109])).

tff(c_374,plain,(
    ! [A_91] :
      ( '#skF_2'(A_91,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_365])).

tff(c_42,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_377,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_374,c_42])).

tff(c_380,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_377])).

tff(c_252,plain,(
    ! [B_79,A_80] :
      ( v4_pre_topc(B_79,A_80)
      | ~ v1_xboole_0(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_256,plain,(
    ! [A_80] :
      ( v4_pre_topc('#skF_4',A_80)
      | ~ v1_xboole_0('#skF_4')
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_77,c_252])).

tff(c_259,plain,(
    ! [A_80] :
      ( v4_pre_topc('#skF_4',A_80)
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_256])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_110,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = '#skF_4'
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_14])).

tff(c_114,plain,(
    ! [B_3] : k4_xboole_0(B_3,B_3) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_110])).

tff(c_144,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_162,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_144])).

tff(c_166,plain,(
    ! [A_6] : k3_xboole_0(A_6,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_162])).

tff(c_219,plain,(
    ! [A_70,B_71,C_72] :
      ( k9_subset_1(A_70,B_71,C_72) = k3_xboole_0(B_71,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_221,plain,(
    ! [A_13,B_71] : k9_subset_1(A_13,B_71,'#skF_4') = k3_xboole_0(B_71,'#skF_4') ),
    inference(resolution,[status(thm)],[c_77,c_219])).

tff(c_223,plain,(
    ! [A_13,B_71] : k9_subset_1(A_13,B_71,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_221])).

tff(c_600,plain,(
    ! [A_108,B_109,D_110] :
      ( k9_subset_1(u1_struct_0(A_108),B_109,D_110) != '#skF_2'(A_108,B_109)
      | ~ v4_pre_topc(D_110,A_108)
      | ~ m1_subset_1(D_110,k1_zfmisc_1(u1_struct_0(A_108)))
      | v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_603,plain,(
    ! [A_108,B_71] :
      ( '#skF_2'(A_108,B_71) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_108)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_108)))
      | v2_tex_2(B_71,A_108)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_600])).

tff(c_606,plain,(
    ! [A_111,B_112] :
      ( '#skF_2'(A_111,B_112) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_111)
      | v2_tex_2(B_112,A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_603])).

tff(c_620,plain,(
    ! [A_113] :
      ( '#skF_2'(A_113,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_113)
      | v2_tex_2('#skF_4',A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_77,c_606])).

tff(c_625,plain,(
    ! [A_114] :
      ( '#skF_2'(A_114,'#skF_4') != '#skF_4'
      | v2_tex_2('#skF_4',A_114)
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_259,c_620])).

tff(c_628,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_625,c_42])).

tff(c_632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_380,c_628])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.42  
% 2.66/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.42  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.66/1.42  
% 2.66/1.42  %Foreground sorts:
% 2.66/1.42  
% 2.66/1.42  
% 2.66/1.42  %Background operators:
% 2.66/1.42  
% 2.66/1.42  
% 2.66/1.42  %Foreground operators:
% 2.66/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.66/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.66/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.66/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.66/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.42  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.66/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.42  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.66/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.66/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.66/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.66/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.66/1.42  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.66/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.42  
% 2.90/1.44  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.90/1.44  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.90/1.44  tff(f_42, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.90/1.44  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.90/1.44  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 2.90/1.44  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.90/1.44  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.90/1.44  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.90/1.44  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.90/1.44  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.90/1.44  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.90/1.44  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.90/1.44  tff(c_46, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.90/1.44  tff(c_65, plain, (![A_49]: (k1_xboole_0=A_49 | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.90/1.44  tff(c_74, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_46, c_65])).
% 2.90/1.44  tff(c_16, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.90/1.44  tff(c_76, plain, (![A_6]: (k4_xboole_0(A_6, '#skF_4')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_16])).
% 2.90/1.44  tff(c_24, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.90/1.44  tff(c_77, plain, (![A_13]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_24])).
% 2.90/1.44  tff(c_352, plain, (![A_88, B_89]: (r1_tarski('#skF_2'(A_88, B_89), B_89) | v2_tex_2(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.90/1.44  tff(c_357, plain, (![A_90]: (r1_tarski('#skF_2'(A_90, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_90) | ~l1_pre_topc(A_90))), inference(resolution, [status(thm)], [c_77, c_352])).
% 2.90/1.44  tff(c_14, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=k1_xboole_0 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.90/1.44  tff(c_109, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)='#skF_4' | ~r1_tarski(A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_14])).
% 2.90/1.44  tff(c_365, plain, (![A_90]: (k4_xboole_0('#skF_2'(A_90, '#skF_4'), '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_90) | ~l1_pre_topc(A_90))), inference(resolution, [status(thm)], [c_357, c_109])).
% 2.90/1.44  tff(c_374, plain, (![A_91]: ('#skF_2'(A_91, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_91) | ~l1_pre_topc(A_91))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_365])).
% 2.90/1.44  tff(c_42, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.90/1.44  tff(c_377, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_374, c_42])).
% 2.90/1.44  tff(c_380, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_377])).
% 2.90/1.44  tff(c_252, plain, (![B_79, A_80]: (v4_pre_topc(B_79, A_80) | ~v1_xboole_0(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.90/1.44  tff(c_256, plain, (![A_80]: (v4_pre_topc('#skF_4', A_80) | ~v1_xboole_0('#skF_4') | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(resolution, [status(thm)], [c_77, c_252])).
% 2.90/1.44  tff(c_259, plain, (![A_80]: (v4_pre_topc('#skF_4', A_80) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_256])).
% 2.90/1.44  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.90/1.44  tff(c_110, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)='#skF_4' | ~r1_tarski(A_54, B_55))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_14])).
% 2.90/1.44  tff(c_114, plain, (![B_3]: (k4_xboole_0(B_3, B_3)='#skF_4')), inference(resolution, [status(thm)], [c_10, c_110])).
% 2.90/1.44  tff(c_144, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.90/1.44  tff(c_162, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_144])).
% 2.90/1.44  tff(c_166, plain, (![A_6]: (k3_xboole_0(A_6, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_162])).
% 2.90/1.44  tff(c_219, plain, (![A_70, B_71, C_72]: (k9_subset_1(A_70, B_71, C_72)=k3_xboole_0(B_71, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.90/1.44  tff(c_221, plain, (![A_13, B_71]: (k9_subset_1(A_13, B_71, '#skF_4')=k3_xboole_0(B_71, '#skF_4'))), inference(resolution, [status(thm)], [c_77, c_219])).
% 2.90/1.44  tff(c_223, plain, (![A_13, B_71]: (k9_subset_1(A_13, B_71, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_221])).
% 2.90/1.44  tff(c_600, plain, (![A_108, B_109, D_110]: (k9_subset_1(u1_struct_0(A_108), B_109, D_110)!='#skF_2'(A_108, B_109) | ~v4_pre_topc(D_110, A_108) | ~m1_subset_1(D_110, k1_zfmisc_1(u1_struct_0(A_108))) | v2_tex_2(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.90/1.44  tff(c_603, plain, (![A_108, B_71]: ('#skF_2'(A_108, B_71)!='#skF_4' | ~v4_pre_topc('#skF_4', A_108) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_108))) | v2_tex_2(B_71, A_108) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(superposition, [status(thm), theory('equality')], [c_223, c_600])).
% 2.90/1.44  tff(c_606, plain, (![A_111, B_112]: ('#skF_2'(A_111, B_112)!='#skF_4' | ~v4_pre_topc('#skF_4', A_111) | v2_tex_2(B_112, A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_603])).
% 2.90/1.44  tff(c_620, plain, (![A_113]: ('#skF_2'(A_113, '#skF_4')!='#skF_4' | ~v4_pre_topc('#skF_4', A_113) | v2_tex_2('#skF_4', A_113) | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_77, c_606])).
% 2.90/1.44  tff(c_625, plain, (![A_114]: ('#skF_2'(A_114, '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', A_114) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114))), inference(resolution, [status(thm)], [c_259, c_620])).
% 2.90/1.44  tff(c_628, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_625, c_42])).
% 2.90/1.44  tff(c_632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_380, c_628])).
% 2.90/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.44  
% 2.90/1.44  Inference rules
% 2.90/1.44  ----------------------
% 2.90/1.44  #Ref     : 0
% 2.90/1.44  #Sup     : 136
% 2.90/1.44  #Fact    : 0
% 2.90/1.44  #Define  : 0
% 2.90/1.44  #Split   : 0
% 2.90/1.44  #Chain   : 0
% 2.90/1.44  #Close   : 0
% 2.90/1.44  
% 2.90/1.44  Ordering : KBO
% 2.90/1.44  
% 2.90/1.44  Simplification rules
% 2.90/1.44  ----------------------
% 2.90/1.44  #Subsume      : 5
% 2.90/1.44  #Demod        : 126
% 2.90/1.44  #Tautology    : 80
% 2.90/1.44  #SimpNegUnit  : 2
% 2.90/1.44  #BackRed      : 4
% 2.90/1.44  
% 2.90/1.44  #Partial instantiations: 0
% 2.90/1.44  #Strategies tried      : 1
% 2.90/1.44  
% 2.90/1.44  Timing (in seconds)
% 2.90/1.44  ----------------------
% 2.90/1.44  Preprocessing        : 0.33
% 2.90/1.44  Parsing              : 0.18
% 2.90/1.44  CNF conversion       : 0.02
% 2.90/1.44  Main loop            : 0.29
% 2.90/1.44  Inferencing          : 0.11
% 2.90/1.44  Reduction            : 0.10
% 2.90/1.44  Demodulation         : 0.08
% 2.90/1.44  BG Simplification    : 0.02
% 2.90/1.44  Subsumption          : 0.05
% 2.90/1.44  Abstraction          : 0.02
% 2.90/1.44  MUC search           : 0.00
% 2.90/1.44  Cooper               : 0.00
% 2.90/1.44  Total                : 0.65
% 2.90/1.44  Index Insertion      : 0.00
% 2.90/1.44  Index Deletion       : 0.00
% 2.90/1.44  Index Matching       : 0.00
% 2.90/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
