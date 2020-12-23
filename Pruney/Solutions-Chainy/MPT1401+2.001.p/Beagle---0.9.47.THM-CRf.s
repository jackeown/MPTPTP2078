%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:29 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   58 (  73 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  153 ( 289 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_setfam_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v3_pre_topc(C,A)
                    & v4_pre_topc(C,A)
                    & r2_hidden(B,C)
                    & r1_tarski(C,k1_connsp_2(A,B)) )
                 => C = k1_connsp_2(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_connsp_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = k1_connsp_2(A,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
                    & ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(E,D)
                        <=> ( v3_pre_topc(E,A)
                            & v4_pre_topc(E,A)
                            & r2_hidden(B,E) ) ) )
                    & k6_setfam_1(u1_struct_0(A),D) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_connsp_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_56,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_52,plain,(
    v3_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_50,plain,(
    v4_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k1_connsp_2(A_60,B_61),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_121,plain,(
    ! [E_96,A_97,B_98] :
      ( r2_hidden(E_96,'#skF_1'(A_97,B_98,k1_connsp_2(A_97,B_98)))
      | ~ r2_hidden(B_98,E_96)
      | ~ v4_pre_topc(E_96,A_97)
      | ~ v3_pre_topc(E_96,A_97)
      | ~ m1_subset_1(E_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_subset_1(k1_connsp_2(A_97,B_98),k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_subset_1(B_98,u1_struct_0(A_97))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_124,plain,(
    ! [E_96,A_60,B_61] :
      ( r2_hidden(E_96,'#skF_1'(A_60,B_61,k1_connsp_2(A_60,B_61)))
      | ~ r2_hidden(B_61,E_96)
      | ~ v4_pre_topc(E_96,A_60)
      | ~ v3_pre_topc(E_96,A_60)
      | ~ m1_subset_1(E_96,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_42,c_121])).

tff(c_96,plain,(
    ! [A_79,B_80] :
      ( m1_subset_1('#skF_1'(A_79,B_80,k1_connsp_2(A_79,B_80)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79))))
      | ~ m1_subset_1(k1_connsp_2(A_79,B_80),k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ m1_subset_1(B_80,u1_struct_0(A_79))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k6_setfam_1(A_3,B_4) = k1_setfam_1(B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(k1_zfmisc_1(A_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_117,plain,(
    ! [A_94,B_95] :
      ( k6_setfam_1(u1_struct_0(A_94),'#skF_1'(A_94,B_95,k1_connsp_2(A_94,B_95))) = k1_setfam_1('#skF_1'(A_94,B_95,k1_connsp_2(A_94,B_95)))
      | ~ m1_subset_1(k1_connsp_2(A_94,B_95),k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(B_95,u1_struct_0(A_94))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_96,c_8])).

tff(c_125,plain,(
    ! [A_99,B_100] :
      ( k6_setfam_1(u1_struct_0(A_99),'#skF_1'(A_99,B_100,k1_connsp_2(A_99,B_100))) = k1_setfam_1('#skF_1'(A_99,B_100,k1_connsp_2(A_99,B_100)))
      | ~ m1_subset_1(B_100,u1_struct_0(A_99))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_42,c_117])).

tff(c_101,plain,(
    ! [A_81,B_82] :
      ( k6_setfam_1(u1_struct_0(A_81),'#skF_1'(A_81,B_82,k1_connsp_2(A_81,B_82))) = k1_connsp_2(A_81,B_82)
      | ~ m1_subset_1(k1_connsp_2(A_81,B_82),k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_104,plain,(
    ! [A_60,B_61] :
      ( k6_setfam_1(u1_struct_0(A_60),'#skF_1'(A_60,B_61,k1_connsp_2(A_60,B_61))) = k1_connsp_2(A_60,B_61)
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_42,c_101])).

tff(c_140,plain,(
    ! [A_101,B_102] :
      ( k1_setfam_1('#skF_1'(A_101,B_102,k1_connsp_2(A_101,B_102))) = k1_connsp_2(A_101,B_102)
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101)
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_104])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k1_setfam_1(B_6),A_5)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_178,plain,(
    ! [A_109,B_110,A_111] :
      ( r1_tarski(k1_connsp_2(A_109,B_110),A_111)
      | ~ r2_hidden(A_111,'#skF_1'(A_109,B_110,k1_connsp_2(A_109,B_110)))
      | ~ m1_subset_1(B_110,u1_struct_0(A_109))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109)
      | ~ m1_subset_1(B_110,u1_struct_0(A_109))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_10])).

tff(c_183,plain,(
    ! [A_112,B_113,E_114] :
      ( r1_tarski(k1_connsp_2(A_112,B_113),E_114)
      | ~ r2_hidden(B_113,E_114)
      | ~ v4_pre_topc(E_114,A_112)
      | ~ v3_pre_topc(E_114,A_112)
      | ~ m1_subset_1(E_114,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ m1_subset_1(B_113,u1_struct_0(A_112))
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_124,c_178])).

tff(c_189,plain,(
    ! [B_113] :
      ( r1_tarski(k1_connsp_2('#skF_3',B_113),'#skF_5')
      | ~ r2_hidden(B_113,'#skF_5')
      | ~ v4_pre_topc('#skF_5','#skF_3')
      | ~ v3_pre_topc('#skF_5','#skF_3')
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_183])).

tff(c_194,plain,(
    ! [B_113] :
      ( r1_tarski(k1_connsp_2('#skF_3',B_113),'#skF_5')
      | ~ r2_hidden(B_113,'#skF_5')
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_52,c_50,c_189])).

tff(c_196,plain,(
    ! [B_115] :
      ( r1_tarski(k1_connsp_2('#skF_3',B_115),'#skF_5')
      | ~ r2_hidden(B_115,'#skF_5')
      | ~ m1_subset_1(B_115,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_194])).

tff(c_44,plain,(
    k1_connsp_2('#skF_3','#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,(
    r1_tarski('#skF_5',k1_connsp_2('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_66,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,
    ( k1_connsp_2('#skF_3','#skF_4') = '#skF_5'
    | ~ r1_tarski(k1_connsp_2('#skF_3','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_66])).

tff(c_76,plain,(
    ~ r1_tarski(k1_connsp_2('#skF_3','#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_70])).

tff(c_199,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_196,c_76])).

tff(c_205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48,c_199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:17:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/2.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/2.46  
% 3.40/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/2.46  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_setfam_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.40/2.46  
% 3.40/2.46  %Foreground sorts:
% 3.40/2.46  
% 3.40/2.46  
% 3.40/2.46  %Background operators:
% 3.40/2.46  
% 3.40/2.46  
% 3.40/2.46  %Foreground operators:
% 3.40/2.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.40/2.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.40/2.46  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.40/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/2.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/2.46  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 3.40/2.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.40/2.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/2.46  tff('#skF_5', type, '#skF_5': $i).
% 3.40/2.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.40/2.46  tff('#skF_3', type, '#skF_3': $i).
% 3.40/2.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.40/2.46  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.40/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/2.46  tff('#skF_4', type, '#skF_4': $i).
% 3.40/2.46  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.40/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/2.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.40/2.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.40/2.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.40/2.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.40/2.46  
% 3.60/2.51  tff(f_105, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((v3_pre_topc(C, A) & v4_pre_topc(C, A)) & r2_hidden(B, C)) & r1_tarski(C, k1_connsp_2(A, B))) => (C = k1_connsp_2(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_connsp_2)).
% 3.60/2.51  tff(f_81, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 3.60/2.51  tff(f_70, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k1_connsp_2(A, B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) & (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(E, D) <=> ((v3_pre_topc(E, A) & v4_pre_topc(E, A)) & r2_hidden(B, E)))))) & (k6_setfam_1(u1_struct_0(A), D) = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_connsp_2)).
% 3.60/2.51  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.60/2.51  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 3.60/2.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.60/2.51  tff(c_56, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.60/2.51  tff(c_48, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.60/2.51  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.60/2.51  tff(c_60, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.60/2.51  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.60/2.51  tff(c_52, plain, (v3_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.60/2.51  tff(c_50, plain, (v4_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.60/2.51  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.60/2.51  tff(c_42, plain, (![A_60, B_61]: (m1_subset_1(k1_connsp_2(A_60, B_61), k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.60/2.51  tff(c_121, plain, (![E_96, A_97, B_98]: (r2_hidden(E_96, '#skF_1'(A_97, B_98, k1_connsp_2(A_97, B_98))) | ~r2_hidden(B_98, E_96) | ~v4_pre_topc(E_96, A_97) | ~v3_pre_topc(E_96, A_97) | ~m1_subset_1(E_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_subset_1(k1_connsp_2(A_97, B_98), k1_zfmisc_1(u1_struct_0(A_97))) | ~m1_subset_1(B_98, u1_struct_0(A_97)) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.60/2.51  tff(c_124, plain, (![E_96, A_60, B_61]: (r2_hidden(E_96, '#skF_1'(A_60, B_61, k1_connsp_2(A_60, B_61))) | ~r2_hidden(B_61, E_96) | ~v4_pre_topc(E_96, A_60) | ~v3_pre_topc(E_96, A_60) | ~m1_subset_1(E_96, k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_42, c_121])).
% 3.60/2.51  tff(c_96, plain, (![A_79, B_80]: (m1_subset_1('#skF_1'(A_79, B_80, k1_connsp_2(A_79, B_80)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79)))) | ~m1_subset_1(k1_connsp_2(A_79, B_80), k1_zfmisc_1(u1_struct_0(A_79))) | ~m1_subset_1(B_80, u1_struct_0(A_79)) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.60/2.51  tff(c_8, plain, (![A_3, B_4]: (k6_setfam_1(A_3, B_4)=k1_setfam_1(B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(k1_zfmisc_1(A_3))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.60/2.51  tff(c_117, plain, (![A_94, B_95]: (k6_setfam_1(u1_struct_0(A_94), '#skF_1'(A_94, B_95, k1_connsp_2(A_94, B_95)))=k1_setfam_1('#skF_1'(A_94, B_95, k1_connsp_2(A_94, B_95))) | ~m1_subset_1(k1_connsp_2(A_94, B_95), k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_subset_1(B_95, u1_struct_0(A_94)) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(resolution, [status(thm)], [c_96, c_8])).
% 3.60/2.51  tff(c_125, plain, (![A_99, B_100]: (k6_setfam_1(u1_struct_0(A_99), '#skF_1'(A_99, B_100, k1_connsp_2(A_99, B_100)))=k1_setfam_1('#skF_1'(A_99, B_100, k1_connsp_2(A_99, B_100))) | ~m1_subset_1(B_100, u1_struct_0(A_99)) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(resolution, [status(thm)], [c_42, c_117])).
% 3.60/2.51  tff(c_101, plain, (![A_81, B_82]: (k6_setfam_1(u1_struct_0(A_81), '#skF_1'(A_81, B_82, k1_connsp_2(A_81, B_82)))=k1_connsp_2(A_81, B_82) | ~m1_subset_1(k1_connsp_2(A_81, B_82), k1_zfmisc_1(u1_struct_0(A_81))) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.60/2.51  tff(c_104, plain, (![A_60, B_61]: (k6_setfam_1(u1_struct_0(A_60), '#skF_1'(A_60, B_61, k1_connsp_2(A_60, B_61)))=k1_connsp_2(A_60, B_61) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_42, c_101])).
% 3.60/2.51  tff(c_140, plain, (![A_101, B_102]: (k1_setfam_1('#skF_1'(A_101, B_102, k1_connsp_2(A_101, B_102)))=k1_connsp_2(A_101, B_102) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101))), inference(superposition, [status(thm), theory('equality')], [c_125, c_104])).
% 3.60/2.51  tff(c_10, plain, (![B_6, A_5]: (r1_tarski(k1_setfam_1(B_6), A_5) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.60/2.51  tff(c_178, plain, (![A_109, B_110, A_111]: (r1_tarski(k1_connsp_2(A_109, B_110), A_111) | ~r2_hidden(A_111, '#skF_1'(A_109, B_110, k1_connsp_2(A_109, B_110))) | ~m1_subset_1(B_110, u1_struct_0(A_109)) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109) | ~m1_subset_1(B_110, u1_struct_0(A_109)) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(superposition, [status(thm), theory('equality')], [c_140, c_10])).
% 3.60/2.51  tff(c_183, plain, (![A_112, B_113, E_114]: (r1_tarski(k1_connsp_2(A_112, B_113), E_114) | ~r2_hidden(B_113, E_114) | ~v4_pre_topc(E_114, A_112) | ~v3_pre_topc(E_114, A_112) | ~m1_subset_1(E_114, k1_zfmisc_1(u1_struct_0(A_112))) | ~m1_subset_1(B_113, u1_struct_0(A_112)) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112) | v2_struct_0(A_112))), inference(resolution, [status(thm)], [c_124, c_178])).
% 3.60/2.51  tff(c_189, plain, (![B_113]: (r1_tarski(k1_connsp_2('#skF_3', B_113), '#skF_5') | ~r2_hidden(B_113, '#skF_5') | ~v4_pre_topc('#skF_5', '#skF_3') | ~v3_pre_topc('#skF_5', '#skF_3') | ~m1_subset_1(B_113, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_183])).
% 3.60/2.51  tff(c_194, plain, (![B_113]: (r1_tarski(k1_connsp_2('#skF_3', B_113), '#skF_5') | ~r2_hidden(B_113, '#skF_5') | ~m1_subset_1(B_113, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_52, c_50, c_189])).
% 3.60/2.51  tff(c_196, plain, (![B_115]: (r1_tarski(k1_connsp_2('#skF_3', B_115), '#skF_5') | ~r2_hidden(B_115, '#skF_5') | ~m1_subset_1(B_115, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_194])).
% 3.60/2.51  tff(c_44, plain, (k1_connsp_2('#skF_3', '#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.60/2.51  tff(c_46, plain, (r1_tarski('#skF_5', k1_connsp_2('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.60/2.51  tff(c_66, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.60/2.51  tff(c_70, plain, (k1_connsp_2('#skF_3', '#skF_4')='#skF_5' | ~r1_tarski(k1_connsp_2('#skF_3', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_46, c_66])).
% 3.60/2.51  tff(c_76, plain, (~r1_tarski(k1_connsp_2('#skF_3', '#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_70])).
% 3.60/2.51  tff(c_199, plain, (~r2_hidden('#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_196, c_76])).
% 3.60/2.51  tff(c_205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_48, c_199])).
% 3.60/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/2.51  
% 3.60/2.51  Inference rules
% 3.60/2.51  ----------------------
% 3.60/2.51  #Ref     : 0
% 3.60/2.51  #Sup     : 32
% 3.60/2.51  #Fact    : 0
% 3.60/2.51  #Define  : 0
% 3.60/2.51  #Split   : 0
% 3.60/2.51  #Chain   : 0
% 3.60/2.51  #Close   : 0
% 3.60/2.51  
% 3.60/2.51  Ordering : KBO
% 3.60/2.51  
% 3.60/2.51  Simplification rules
% 3.60/2.51  ----------------------
% 3.60/2.51  #Subsume      : 4
% 3.60/2.51  #Demod        : 8
% 3.60/2.51  #Tautology    : 16
% 3.60/2.51  #SimpNegUnit  : 2
% 3.60/2.51  #BackRed      : 0
% 3.60/2.51  
% 3.60/2.51  #Partial instantiations: 0
% 3.60/2.51  #Strategies tried      : 1
% 3.60/2.51  
% 3.60/2.51  Timing (in seconds)
% 3.60/2.51  ----------------------
% 3.60/2.52  Preprocessing        : 0.80
% 3.60/2.52  Parsing              : 0.37
% 3.60/2.52  CNF conversion       : 0.08
% 3.60/2.52  Main loop            : 0.60
% 3.60/2.52  Inferencing          : 0.21
% 3.60/2.52  Reduction            : 0.20
% 3.60/2.52  Demodulation         : 0.14
% 3.60/2.52  BG Simplification    : 0.07
% 3.60/2.52  Subsumption          : 0.12
% 3.60/2.52  Abstraction          : 0.05
% 3.60/2.52  MUC search           : 0.00
% 3.60/2.52  Cooper               : 0.00
% 3.60/2.52  Total                : 1.48
% 3.60/2.52  Index Insertion      : 0.00
% 3.60/2.52  Index Deletion       : 0.00
% 3.60/2.52  Index Matching       : 0.00
% 3.60/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
