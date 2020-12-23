%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:26 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 202 expanded)
%              Number of leaves         :   30 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  114 ( 462 expanded)
%              Number of equality atoms :   22 (  89 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

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
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_34,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_38,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_54,plain,(
    ! [A_48] :
      ( k1_xboole_0 = A_48
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_54])).

tff(c_6,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    ! [A_4] : k3_xboole_0(A_4,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_6])).

tff(c_16,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_65,plain,(
    ! [A_12] : m1_subset_1('#skF_5',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_16])).

tff(c_127,plain,(
    ! [A_70,B_71] :
      ( r1_tarski('#skF_3'(A_70,B_71),B_71)
      | v2_tex_2(B_71,A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_146,plain,(
    ! [A_74] :
      ( r1_tarski('#skF_3'(A_74,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_65,c_127])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( k3_xboole_0(A_2,B_3) = A_2
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_149,plain,(
    ! [A_74] :
      ( k3_xboole_0('#skF_3'(A_74,'#skF_5'),'#skF_5') = '#skF_3'(A_74,'#skF_5')
      | v2_tex_2('#skF_5',A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_146,c_4])).

tff(c_152,plain,(
    ! [A_75] :
      ( '#skF_3'(A_75,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_149])).

tff(c_155,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_152,c_34])).

tff(c_158,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_155])).

tff(c_42,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_132,plain,(
    ! [A_72,B_73] :
      ( m1_subset_1('#skF_3'(A_72,B_73),k1_zfmisc_1(u1_struct_0(A_72)))
      | v2_tex_2(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    ! [B_18,A_16] :
      ( v3_pre_topc(B_18,A_16)
      | ~ v1_xboole_0(B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_186,plain,(
    ! [A_79,B_80] :
      ( v3_pre_topc('#skF_3'(A_79,B_80),A_79)
      | ~ v1_xboole_0('#skF_3'(A_79,B_80))
      | ~ v2_pre_topc(A_79)
      | v2_tex_2(B_80,A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_132,c_20])).

tff(c_194,plain,(
    ! [A_81] :
      ( v3_pre_topc('#skF_3'(A_81,'#skF_5'),A_81)
      | ~ v1_xboole_0('#skF_3'(A_81,'#skF_5'))
      | ~ v2_pre_topc(A_81)
      | v2_tex_2('#skF_5',A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_65,c_186])).

tff(c_197,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ v1_xboole_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_4')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_194])).

tff(c_199,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_38,c_158,c_197])).

tff(c_200,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_199])).

tff(c_105,plain,(
    ! [A_60,B_61,C_62] :
      ( k9_subset_1(A_60,B_61,C_62) = k3_xboole_0(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_107,plain,(
    ! [A_12,B_61] : k9_subset_1(A_12,B_61,'#skF_5') = k3_xboole_0(B_61,'#skF_5') ),
    inference(resolution,[status(thm)],[c_65,c_105])).

tff(c_109,plain,(
    ! [A_12,B_61] : k9_subset_1(A_12,B_61,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_107])).

tff(c_243,plain,(
    ! [A_93,B_94,D_95] :
      ( k9_subset_1(u1_struct_0(A_93),B_94,D_95) != '#skF_3'(A_93,B_94)
      | ~ v3_pre_topc(D_95,A_93)
      | ~ m1_subset_1(D_95,k1_zfmisc_1(u1_struct_0(A_93)))
      | v2_tex_2(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_248,plain,(
    ! [A_93,B_61] :
      ( '#skF_3'(A_93,B_61) != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_93)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_93)))
      | v2_tex_2(B_61,A_93)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_243])).

tff(c_251,plain,(
    ! [A_96,B_97] :
      ( '#skF_3'(A_96,B_97) != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_96)
      | v2_tex_2(B_97,A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_248])).

tff(c_261,plain,(
    ! [A_98] :
      ( '#skF_3'(A_98,'#skF_5') != '#skF_5'
      | ~ v3_pre_topc('#skF_5',A_98)
      | v2_tex_2('#skF_5',A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_65,c_251])).

tff(c_264,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_200,c_261])).

tff(c_270,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_158,c_264])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:25:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.26  
% 2.22/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.27  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.22/1.27  
% 2.22/1.27  %Foreground sorts:
% 2.22/1.27  
% 2.22/1.27  
% 2.22/1.27  %Background operators:
% 2.22/1.27  
% 2.22/1.27  
% 2.22/1.27  %Foreground operators:
% 2.22/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.22/1.27  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.22/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.22/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.22/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.22/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.27  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.22/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.22/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.22/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.22/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.27  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.22/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.27  
% 2.40/1.28  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.40/1.28  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.40/1.28  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.40/1.28  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.40/1.28  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 2.40/1.28  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.40/1.28  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tops_1)).
% 2.40/1.28  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.40/1.28  tff(c_34, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.40/1.28  tff(c_40, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.40/1.28  tff(c_38, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.40/1.28  tff(c_54, plain, (![A_48]: (k1_xboole_0=A_48 | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.40/1.28  tff(c_62, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_38, c_54])).
% 2.40/1.28  tff(c_6, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.40/1.28  tff(c_64, plain, (![A_4]: (k3_xboole_0(A_4, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_6])).
% 2.40/1.28  tff(c_16, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.40/1.28  tff(c_65, plain, (![A_12]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_16])).
% 2.40/1.28  tff(c_127, plain, (![A_70, B_71]: (r1_tarski('#skF_3'(A_70, B_71), B_71) | v2_tex_2(B_71, A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.40/1.28  tff(c_146, plain, (![A_74]: (r1_tarski('#skF_3'(A_74, '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', A_74) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_65, c_127])).
% 2.40/1.28  tff(c_4, plain, (![A_2, B_3]: (k3_xboole_0(A_2, B_3)=A_2 | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.40/1.28  tff(c_149, plain, (![A_74]: (k3_xboole_0('#skF_3'(A_74, '#skF_5'), '#skF_5')='#skF_3'(A_74, '#skF_5') | v2_tex_2('#skF_5', A_74) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_146, c_4])).
% 2.40/1.28  tff(c_152, plain, (![A_75]: ('#skF_3'(A_75, '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_75) | ~l1_pre_topc(A_75))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_149])).
% 2.40/1.28  tff(c_155, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_152, c_34])).
% 2.40/1.28  tff(c_158, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_155])).
% 2.40/1.28  tff(c_42, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.40/1.28  tff(c_132, plain, (![A_72, B_73]: (m1_subset_1('#skF_3'(A_72, B_73), k1_zfmisc_1(u1_struct_0(A_72))) | v2_tex_2(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.40/1.28  tff(c_20, plain, (![B_18, A_16]: (v3_pre_topc(B_18, A_16) | ~v1_xboole_0(B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.40/1.28  tff(c_186, plain, (![A_79, B_80]: (v3_pre_topc('#skF_3'(A_79, B_80), A_79) | ~v1_xboole_0('#skF_3'(A_79, B_80)) | ~v2_pre_topc(A_79) | v2_tex_2(B_80, A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_132, c_20])).
% 2.40/1.28  tff(c_194, plain, (![A_81]: (v3_pre_topc('#skF_3'(A_81, '#skF_5'), A_81) | ~v1_xboole_0('#skF_3'(A_81, '#skF_5')) | ~v2_pre_topc(A_81) | v2_tex_2('#skF_5', A_81) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_65, c_186])).
% 2.40/1.28  tff(c_197, plain, (v3_pre_topc('#skF_5', '#skF_4') | ~v1_xboole_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_4') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_158, c_194])).
% 2.40/1.28  tff(c_199, plain, (v3_pre_topc('#skF_5', '#skF_4') | v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_38, c_158, c_197])).
% 2.40/1.28  tff(c_200, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_199])).
% 2.40/1.28  tff(c_105, plain, (![A_60, B_61, C_62]: (k9_subset_1(A_60, B_61, C_62)=k3_xboole_0(B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.40/1.28  tff(c_107, plain, (![A_12, B_61]: (k9_subset_1(A_12, B_61, '#skF_5')=k3_xboole_0(B_61, '#skF_5'))), inference(resolution, [status(thm)], [c_65, c_105])).
% 2.40/1.28  tff(c_109, plain, (![A_12, B_61]: (k9_subset_1(A_12, B_61, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_107])).
% 2.40/1.28  tff(c_243, plain, (![A_93, B_94, D_95]: (k9_subset_1(u1_struct_0(A_93), B_94, D_95)!='#skF_3'(A_93, B_94) | ~v3_pre_topc(D_95, A_93) | ~m1_subset_1(D_95, k1_zfmisc_1(u1_struct_0(A_93))) | v2_tex_2(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.40/1.28  tff(c_248, plain, (![A_93, B_61]: ('#skF_3'(A_93, B_61)!='#skF_5' | ~v3_pre_topc('#skF_5', A_93) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_93))) | v2_tex_2(B_61, A_93) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(superposition, [status(thm), theory('equality')], [c_109, c_243])).
% 2.40/1.28  tff(c_251, plain, (![A_96, B_97]: ('#skF_3'(A_96, B_97)!='#skF_5' | ~v3_pre_topc('#skF_5', A_96) | v2_tex_2(B_97, A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_248])).
% 2.40/1.28  tff(c_261, plain, (![A_98]: ('#skF_3'(A_98, '#skF_5')!='#skF_5' | ~v3_pre_topc('#skF_5', A_98) | v2_tex_2('#skF_5', A_98) | ~l1_pre_topc(A_98))), inference(resolution, [status(thm)], [c_65, c_251])).
% 2.40/1.28  tff(c_264, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_200, c_261])).
% 2.40/1.28  tff(c_270, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_158, c_264])).
% 2.40/1.28  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_270])).
% 2.40/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.28  
% 2.40/1.28  Inference rules
% 2.40/1.28  ----------------------
% 2.40/1.28  #Ref     : 0
% 2.40/1.28  #Sup     : 48
% 2.40/1.28  #Fact    : 0
% 2.40/1.28  #Define  : 0
% 2.40/1.28  #Split   : 0
% 2.40/1.28  #Chain   : 0
% 2.40/1.28  #Close   : 0
% 2.40/1.28  
% 2.40/1.28  Ordering : KBO
% 2.40/1.28  
% 2.40/1.28  Simplification rules
% 2.40/1.28  ----------------------
% 2.40/1.28  #Subsume      : 2
% 2.40/1.28  #Demod        : 33
% 2.40/1.28  #Tautology    : 21
% 2.40/1.28  #SimpNegUnit  : 6
% 2.40/1.28  #BackRed      : 4
% 2.40/1.28  
% 2.40/1.28  #Partial instantiations: 0
% 2.40/1.28  #Strategies tried      : 1
% 2.40/1.28  
% 2.40/1.28  Timing (in seconds)
% 2.40/1.28  ----------------------
% 2.40/1.28  Preprocessing        : 0.31
% 2.40/1.28  Parsing              : 0.16
% 2.40/1.28  CNF conversion       : 0.02
% 2.40/1.28  Main loop            : 0.20
% 2.40/1.28  Inferencing          : 0.08
% 2.40/1.28  Reduction            : 0.06
% 2.40/1.28  Demodulation         : 0.04
% 2.40/1.28  BG Simplification    : 0.01
% 2.40/1.28  Subsumption          : 0.03
% 2.40/1.28  Abstraction          : 0.01
% 2.40/1.28  MUC search           : 0.00
% 2.40/1.28  Cooper               : 0.00
% 2.40/1.28  Total                : 0.54
% 2.40/1.28  Index Insertion      : 0.00
% 2.40/1.28  Index Deletion       : 0.00
% 2.40/1.28  Index Matching       : 0.00
% 2.40/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
