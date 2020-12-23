%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:29 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   54 (  71 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  175 ( 304 expanded)
%              Number of equality atoms :    4 (  14 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tops_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_setfam_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v4_pre_topc(k1_connsp_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_connsp_2)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_81,axiom,(
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

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
           => v4_pre_topc(k6_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_2)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_50,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1(k1_connsp_2(A_67,B_68),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    ! [A_14,B_42] :
      ( m1_subset_1('#skF_2'(A_14,B_42,k1_connsp_2(A_14,B_42)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_14))))
      | ~ m1_subset_1(k1_connsp_2(A_14,B_42),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_42,u1_struct_0(A_14))
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8,plain,(
    ! [A_1,B_7] :
      ( m1_subset_1('#skF_1'(A_1,B_7),k1_zfmisc_1(u1_struct_0(A_1)))
      | v2_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1('#skF_2'(A_83,B_84,k1_connsp_2(A_83,B_84)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_83))))
      | ~ m1_subset_1(k1_connsp_2(A_83,B_84),k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ m1_subset_1(B_84,u1_struct_0(A_83))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_1,B_7] :
      ( r2_hidden('#skF_1'(A_1,B_7),B_7)
      | v2_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_107,plain,(
    ! [A_109,B_110] :
      ( r2_hidden('#skF_1'(A_109,'#skF_2'(A_109,B_110,k1_connsp_2(A_109,B_110))),'#skF_2'(A_109,B_110,k1_connsp_2(A_109,B_110)))
      | v2_tops_2('#skF_2'(A_109,B_110,k1_connsp_2(A_109,B_110)),A_109)
      | ~ m1_subset_1(k1_connsp_2(A_109,B_110),k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m1_subset_1(B_110,u1_struct_0(A_109))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(resolution,[status(thm)],[c_59,c_6])).

tff(c_38,plain,(
    ! [E_64,A_14,B_42] :
      ( v4_pre_topc(E_64,A_14)
      | ~ r2_hidden(E_64,'#skF_2'(A_14,B_42,k1_connsp_2(A_14,B_42)))
      | ~ m1_subset_1(E_64,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(k1_connsp_2(A_14,B_42),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ m1_subset_1(B_42,u1_struct_0(A_14))
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_121,plain,(
    ! [A_113,B_114] :
      ( v4_pre_topc('#skF_1'(A_113,'#skF_2'(A_113,B_114,k1_connsp_2(A_113,B_114))),A_113)
      | ~ m1_subset_1('#skF_1'(A_113,'#skF_2'(A_113,B_114,k1_connsp_2(A_113,B_114))),k1_zfmisc_1(u1_struct_0(A_113)))
      | v2_tops_2('#skF_2'(A_113,B_114,k1_connsp_2(A_113,B_114)),A_113)
      | ~ m1_subset_1(k1_connsp_2(A_113,B_114),k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_107,c_38])).

tff(c_127,plain,(
    ! [A_115,B_116] :
      ( v4_pre_topc('#skF_1'(A_115,'#skF_2'(A_115,B_116,k1_connsp_2(A_115,B_116))),A_115)
      | ~ m1_subset_1(k1_connsp_2(A_115,B_116),k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ m1_subset_1(B_116,u1_struct_0(A_115))
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115)
      | v2_tops_2('#skF_2'(A_115,B_116,k1_connsp_2(A_115,B_116)),A_115)
      | ~ m1_subset_1('#skF_2'(A_115,B_116,k1_connsp_2(A_115,B_116)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_115))))
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_8,c_121])).

tff(c_134,plain,(
    ! [A_120,B_121] :
      ( v4_pre_topc('#skF_1'(A_120,'#skF_2'(A_120,B_121,k1_connsp_2(A_120,B_121))),A_120)
      | v2_tops_2('#skF_2'(A_120,B_121,k1_connsp_2(A_120,B_121)),A_120)
      | ~ m1_subset_1(k1_connsp_2(A_120,B_121),k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(B_121,u1_struct_0(A_120))
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120)
      | v2_struct_0(A_120) ) ),
    inference(resolution,[status(thm)],[c_32,c_127])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( ~ v4_pre_topc('#skF_1'(A_1,B_7),A_1)
      | v2_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_138,plain,(
    ! [A_122,B_123] :
      ( ~ m1_subset_1('#skF_2'(A_122,B_123,k1_connsp_2(A_122,B_123)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_122))))
      | v2_tops_2('#skF_2'(A_122,B_123,k1_connsp_2(A_122,B_123)),A_122)
      | ~ m1_subset_1(k1_connsp_2(A_122,B_123),k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m1_subset_1(B_123,u1_struct_0(A_122))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_134,c_4])).

tff(c_143,plain,(
    ! [A_124,B_125] :
      ( v2_tops_2('#skF_2'(A_124,B_125,k1_connsp_2(A_124,B_125)),A_124)
      | ~ m1_subset_1(k1_connsp_2(A_124,B_125),k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ m1_subset_1(B_125,u1_struct_0(A_124))
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124) ) ),
    inference(resolution,[status(thm)],[c_32,c_138])).

tff(c_150,plain,(
    ! [A_129,B_130] :
      ( v2_tops_2('#skF_2'(A_129,B_130,k1_connsp_2(A_129,B_130)),A_129)
      | ~ m1_subset_1(B_130,u1_struct_0(A_129))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_42,c_143])).

tff(c_66,plain,(
    ! [A_85,B_86] :
      ( k6_setfam_1(u1_struct_0(A_85),'#skF_2'(A_85,B_86,k1_connsp_2(A_85,B_86))) = k1_connsp_2(A_85,B_86)
      | ~ m1_subset_1(k1_connsp_2(A_85,B_86),k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ m1_subset_1(B_86,u1_struct_0(A_85))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_69,plain,(
    ! [A_67,B_68] :
      ( k6_setfam_1(u1_struct_0(A_67),'#skF_2'(A_67,B_68,k1_connsp_2(A_67,B_68))) = k1_connsp_2(A_67,B_68)
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_42,c_66])).

tff(c_10,plain,(
    ! [A_11,B_13] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(A_11),B_13),A_11)
      | ~ v2_tops_2(B_13,A_11)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,(
    ! [A_98,B_99] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(A_98),'#skF_2'(A_98,B_99,k1_connsp_2(A_98,B_99))),A_98)
      | ~ v2_tops_2('#skF_2'(A_98,B_99,k1_connsp_2(A_98,B_99)),A_98)
      | ~ m1_subset_1(k1_connsp_2(A_98,B_99),k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ m1_subset_1(B_99,u1_struct_0(A_98))
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_59,c_10])).

tff(c_85,plain,(
    ! [A_67,B_68] :
      ( v4_pre_topc(k1_connsp_2(A_67,B_68),A_67)
      | ~ v2_tops_2('#skF_2'(A_67,B_68,k1_connsp_2(A_67,B_68)),A_67)
      | ~ m1_subset_1(k1_connsp_2(A_67,B_68),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67)
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_82])).

tff(c_154,plain,(
    ! [A_131,B_132] :
      ( v4_pre_topc(k1_connsp_2(A_131,B_132),A_131)
      | ~ m1_subset_1(k1_connsp_2(A_131,B_132),k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(resolution,[status(thm)],[c_150,c_85])).

tff(c_159,plain,(
    ! [A_133,B_134] :
      ( v4_pre_topc(k1_connsp_2(A_133,B_134),A_133)
      | ~ m1_subset_1(B_134,u1_struct_0(A_133))
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133) ) ),
    inference(resolution,[status(thm)],[c_42,c_154])).

tff(c_44,plain,(
    ~ v4_pre_topc(k1_connsp_2('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_162,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_159,c_44])).

tff(c_165,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_162])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.34  
% 2.32/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.34  %$ v4_pre_topc > v3_pre_topc > v2_tops_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_setfam_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.32/1.34  
% 2.32/1.34  %Foreground sorts:
% 2.32/1.34  
% 2.32/1.34  
% 2.32/1.34  %Background operators:
% 2.32/1.34  
% 2.32/1.34  
% 2.32/1.34  %Foreground operators:
% 2.32/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.32/1.34  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.32/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.34  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 2.32/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.32/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.32/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.32/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.34  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.32/1.34  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.32/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.34  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.32/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.32/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.32/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.32/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.32/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.34  
% 2.58/1.35  tff(f_105, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v4_pre_topc(k1_connsp_2(A, B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_connsp_2)).
% 2.58/1.35  tff(f_92, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 2.58/1.35  tff(f_81, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k1_connsp_2(A, B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) & (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(E, D) <=> ((v3_pre_topc(E, A) & v4_pre_topc(E, A)) & r2_hidden(B, E)))))) & (k6_setfam_1(u1_struct_0(A), D) = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_connsp_2)).
% 2.58/1.35  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_2)).
% 2.58/1.35  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v4_pre_topc(k6_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_2)).
% 2.58/1.35  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.58/1.35  tff(c_50, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.58/1.35  tff(c_48, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.58/1.35  tff(c_46, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.58/1.35  tff(c_42, plain, (![A_67, B_68]: (m1_subset_1(k1_connsp_2(A_67, B_68), k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_subset_1(B_68, u1_struct_0(A_67)) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.58/1.35  tff(c_32, plain, (![A_14, B_42]: (m1_subset_1('#skF_2'(A_14, B_42, k1_connsp_2(A_14, B_42)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_14)))) | ~m1_subset_1(k1_connsp_2(A_14, B_42), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_42, u1_struct_0(A_14)) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.58/1.35  tff(c_8, plain, (![A_1, B_7]: (m1_subset_1('#skF_1'(A_1, B_7), k1_zfmisc_1(u1_struct_0(A_1))) | v2_tops_2(B_7, A_1) | ~m1_subset_1(B_7, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.58/1.35  tff(c_59, plain, (![A_83, B_84]: (m1_subset_1('#skF_2'(A_83, B_84, k1_connsp_2(A_83, B_84)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_83)))) | ~m1_subset_1(k1_connsp_2(A_83, B_84), k1_zfmisc_1(u1_struct_0(A_83))) | ~m1_subset_1(B_84, u1_struct_0(A_83)) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.58/1.35  tff(c_6, plain, (![A_1, B_7]: (r2_hidden('#skF_1'(A_1, B_7), B_7) | v2_tops_2(B_7, A_1) | ~m1_subset_1(B_7, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.58/1.35  tff(c_107, plain, (![A_109, B_110]: (r2_hidden('#skF_1'(A_109, '#skF_2'(A_109, B_110, k1_connsp_2(A_109, B_110))), '#skF_2'(A_109, B_110, k1_connsp_2(A_109, B_110))) | v2_tops_2('#skF_2'(A_109, B_110, k1_connsp_2(A_109, B_110)), A_109) | ~m1_subset_1(k1_connsp_2(A_109, B_110), k1_zfmisc_1(u1_struct_0(A_109))) | ~m1_subset_1(B_110, u1_struct_0(A_109)) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(resolution, [status(thm)], [c_59, c_6])).
% 2.58/1.35  tff(c_38, plain, (![E_64, A_14, B_42]: (v4_pre_topc(E_64, A_14) | ~r2_hidden(E_64, '#skF_2'(A_14, B_42, k1_connsp_2(A_14, B_42))) | ~m1_subset_1(E_64, k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(k1_connsp_2(A_14, B_42), k1_zfmisc_1(u1_struct_0(A_14))) | ~m1_subset_1(B_42, u1_struct_0(A_14)) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.58/1.35  tff(c_121, plain, (![A_113, B_114]: (v4_pre_topc('#skF_1'(A_113, '#skF_2'(A_113, B_114, k1_connsp_2(A_113, B_114))), A_113) | ~m1_subset_1('#skF_1'(A_113, '#skF_2'(A_113, B_114, k1_connsp_2(A_113, B_114))), k1_zfmisc_1(u1_struct_0(A_113))) | v2_tops_2('#skF_2'(A_113, B_114, k1_connsp_2(A_113, B_114)), A_113) | ~m1_subset_1(k1_connsp_2(A_113, B_114), k1_zfmisc_1(u1_struct_0(A_113))) | ~m1_subset_1(B_114, u1_struct_0(A_113)) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113))), inference(resolution, [status(thm)], [c_107, c_38])).
% 2.58/1.35  tff(c_127, plain, (![A_115, B_116]: (v4_pre_topc('#skF_1'(A_115, '#skF_2'(A_115, B_116, k1_connsp_2(A_115, B_116))), A_115) | ~m1_subset_1(k1_connsp_2(A_115, B_116), k1_zfmisc_1(u1_struct_0(A_115))) | ~m1_subset_1(B_116, u1_struct_0(A_115)) | ~v2_pre_topc(A_115) | v2_struct_0(A_115) | v2_tops_2('#skF_2'(A_115, B_116, k1_connsp_2(A_115, B_116)), A_115) | ~m1_subset_1('#skF_2'(A_115, B_116, k1_connsp_2(A_115, B_116)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_115)))) | ~l1_pre_topc(A_115))), inference(resolution, [status(thm)], [c_8, c_121])).
% 2.58/1.35  tff(c_134, plain, (![A_120, B_121]: (v4_pre_topc('#skF_1'(A_120, '#skF_2'(A_120, B_121, k1_connsp_2(A_120, B_121))), A_120) | v2_tops_2('#skF_2'(A_120, B_121, k1_connsp_2(A_120, B_121)), A_120) | ~m1_subset_1(k1_connsp_2(A_120, B_121), k1_zfmisc_1(u1_struct_0(A_120))) | ~m1_subset_1(B_121, u1_struct_0(A_120)) | ~l1_pre_topc(A_120) | ~v2_pre_topc(A_120) | v2_struct_0(A_120))), inference(resolution, [status(thm)], [c_32, c_127])).
% 2.58/1.35  tff(c_4, plain, (![A_1, B_7]: (~v4_pre_topc('#skF_1'(A_1, B_7), A_1) | v2_tops_2(B_7, A_1) | ~m1_subset_1(B_7, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.58/1.35  tff(c_138, plain, (![A_122, B_123]: (~m1_subset_1('#skF_2'(A_122, B_123, k1_connsp_2(A_122, B_123)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_122)))) | v2_tops_2('#skF_2'(A_122, B_123, k1_connsp_2(A_122, B_123)), A_122) | ~m1_subset_1(k1_connsp_2(A_122, B_123), k1_zfmisc_1(u1_struct_0(A_122))) | ~m1_subset_1(B_123, u1_struct_0(A_122)) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(resolution, [status(thm)], [c_134, c_4])).
% 2.58/1.35  tff(c_143, plain, (![A_124, B_125]: (v2_tops_2('#skF_2'(A_124, B_125, k1_connsp_2(A_124, B_125)), A_124) | ~m1_subset_1(k1_connsp_2(A_124, B_125), k1_zfmisc_1(u1_struct_0(A_124))) | ~m1_subset_1(B_125, u1_struct_0(A_124)) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124) | v2_struct_0(A_124))), inference(resolution, [status(thm)], [c_32, c_138])).
% 2.58/1.35  tff(c_150, plain, (![A_129, B_130]: (v2_tops_2('#skF_2'(A_129, B_130, k1_connsp_2(A_129, B_130)), A_129) | ~m1_subset_1(B_130, u1_struct_0(A_129)) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129))), inference(resolution, [status(thm)], [c_42, c_143])).
% 2.58/1.35  tff(c_66, plain, (![A_85, B_86]: (k6_setfam_1(u1_struct_0(A_85), '#skF_2'(A_85, B_86, k1_connsp_2(A_85, B_86)))=k1_connsp_2(A_85, B_86) | ~m1_subset_1(k1_connsp_2(A_85, B_86), k1_zfmisc_1(u1_struct_0(A_85))) | ~m1_subset_1(B_86, u1_struct_0(A_85)) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.58/1.35  tff(c_69, plain, (![A_67, B_68]: (k6_setfam_1(u1_struct_0(A_67), '#skF_2'(A_67, B_68, k1_connsp_2(A_67, B_68)))=k1_connsp_2(A_67, B_68) | ~m1_subset_1(B_68, u1_struct_0(A_67)) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(resolution, [status(thm)], [c_42, c_66])).
% 2.58/1.35  tff(c_10, plain, (![A_11, B_13]: (v4_pre_topc(k6_setfam_1(u1_struct_0(A_11), B_13), A_11) | ~v2_tops_2(B_13, A_11) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11)))) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.58/1.35  tff(c_82, plain, (![A_98, B_99]: (v4_pre_topc(k6_setfam_1(u1_struct_0(A_98), '#skF_2'(A_98, B_99, k1_connsp_2(A_98, B_99))), A_98) | ~v2_tops_2('#skF_2'(A_98, B_99, k1_connsp_2(A_98, B_99)), A_98) | ~m1_subset_1(k1_connsp_2(A_98, B_99), k1_zfmisc_1(u1_struct_0(A_98))) | ~m1_subset_1(B_99, u1_struct_0(A_98)) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(resolution, [status(thm)], [c_59, c_10])).
% 2.58/1.35  tff(c_85, plain, (![A_67, B_68]: (v4_pre_topc(k1_connsp_2(A_67, B_68), A_67) | ~v2_tops_2('#skF_2'(A_67, B_68, k1_connsp_2(A_67, B_68)), A_67) | ~m1_subset_1(k1_connsp_2(A_67, B_68), k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_subset_1(B_68, u1_struct_0(A_67)) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67) | ~m1_subset_1(B_68, u1_struct_0(A_67)) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(superposition, [status(thm), theory('equality')], [c_69, c_82])).
% 2.58/1.35  tff(c_154, plain, (![A_131, B_132]: (v4_pre_topc(k1_connsp_2(A_131, B_132), A_131) | ~m1_subset_1(k1_connsp_2(A_131, B_132), k1_zfmisc_1(u1_struct_0(A_131))) | ~m1_subset_1(B_132, u1_struct_0(A_131)) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(resolution, [status(thm)], [c_150, c_85])).
% 2.58/1.35  tff(c_159, plain, (![A_133, B_134]: (v4_pre_topc(k1_connsp_2(A_133, B_134), A_133) | ~m1_subset_1(B_134, u1_struct_0(A_133)) | ~l1_pre_topc(A_133) | ~v2_pre_topc(A_133) | v2_struct_0(A_133))), inference(resolution, [status(thm)], [c_42, c_154])).
% 2.58/1.35  tff(c_44, plain, (~v4_pre_topc(k1_connsp_2('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.58/1.35  tff(c_162, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_159, c_44])).
% 2.58/1.35  tff(c_165, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_162])).
% 2.58/1.35  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_165])).
% 2.58/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.35  
% 2.58/1.35  Inference rules
% 2.58/1.35  ----------------------
% 2.58/1.35  #Ref     : 0
% 2.58/1.35  #Sup     : 26
% 2.58/1.35  #Fact    : 0
% 2.58/1.35  #Define  : 0
% 2.58/1.35  #Split   : 0
% 2.58/1.35  #Chain   : 0
% 2.58/1.35  #Close   : 0
% 2.58/1.35  
% 2.58/1.35  Ordering : KBO
% 2.58/1.35  
% 2.58/1.35  Simplification rules
% 2.58/1.35  ----------------------
% 2.58/1.35  #Subsume      : 10
% 2.58/1.35  #Demod        : 3
% 2.58/1.35  #Tautology    : 9
% 2.58/1.35  #SimpNegUnit  : 1
% 2.58/1.35  #BackRed      : 0
% 2.58/1.35  
% 2.58/1.35  #Partial instantiations: 0
% 2.58/1.36  #Strategies tried      : 1
% 2.58/1.36  
% 2.58/1.36  Timing (in seconds)
% 2.58/1.36  ----------------------
% 2.58/1.36  Preprocessing        : 0.33
% 2.58/1.36  Parsing              : 0.17
% 2.58/1.36  CNF conversion       : 0.03
% 2.58/1.36  Main loop            : 0.21
% 2.58/1.36  Inferencing          : 0.09
% 2.58/1.36  Reduction            : 0.05
% 2.58/1.36  Demodulation         : 0.04
% 2.58/1.36  BG Simplification    : 0.02
% 2.58/1.36  Subsumption          : 0.05
% 2.58/1.36  Abstraction          : 0.01
% 2.58/1.36  MUC search           : 0.00
% 2.58/1.36  Cooper               : 0.00
% 2.58/1.36  Total                : 0.58
% 2.58/1.36  Index Insertion      : 0.00
% 2.58/1.36  Index Deletion       : 0.00
% 2.58/1.36  Index Matching       : 0.00
% 2.58/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
