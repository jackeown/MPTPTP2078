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
% DateTime   : Thu Dec  3 10:24:29 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   49 (  67 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  162 ( 298 expanded)
%              Number of equality atoms :    4 (  16 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_setfam_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v4_pre_topc(k1_connsp_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_connsp_2)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_72,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_connsp_2)).

tff(f_41,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_pre_topc)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_46,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_38,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k1_connsp_2(A_60,B_61),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_60,plain,(
    ! [A_73,B_74] :
      ( k6_setfam_1(u1_struct_0(A_73),'#skF_2'(A_73,B_74,k1_connsp_2(A_73,B_74))) = k1_connsp_2(A_73,B_74)
      | ~ m1_subset_1(k1_connsp_2(A_73,B_74),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_63,plain,(
    ! [A_60,B_61] :
      ( k6_setfam_1(u1_struct_0(A_60),'#skF_2'(A_60,B_61,k1_connsp_2(A_60,B_61))) = k1_connsp_2(A_60,B_61)
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_38,c_60])).

tff(c_28,plain,(
    ! [A_7,B_35] :
      ( m1_subset_1('#skF_2'(A_7,B_35,k1_connsp_2(A_7,B_35)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7))))
      | ~ m1_subset_1(k1_connsp_2(A_7,B_35),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_35,u1_struct_0(A_7))
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_1,B_5] :
      ( m1_subset_1('#skF_1'(A_1,B_5),k1_zfmisc_1(u1_struct_0(A_1)))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_1),B_5),A_1)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1('#skF_2'(A_71,B_72,k1_connsp_2(A_71,B_72)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_71))))
      | ~ m1_subset_1(k1_connsp_2(A_71,B_72),k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ m1_subset_1(B_72,u1_struct_0(A_71))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [A_1,B_5] :
      ( r2_hidden('#skF_1'(A_1,B_5),B_5)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_1),B_5),A_1)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_1'(A_99,'#skF_2'(A_99,B_100,k1_connsp_2(A_99,B_100))),'#skF_2'(A_99,B_100,k1_connsp_2(A_99,B_100)))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_99),'#skF_2'(A_99,B_100,k1_connsp_2(A_99,B_100))),A_99)
      | ~ m1_subset_1(k1_connsp_2(A_99,B_100),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_subset_1(B_100,u1_struct_0(A_99))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_53,c_4])).

tff(c_34,plain,(
    ! [E_57,A_7,B_35] :
      ( v4_pre_topc(E_57,A_7)
      | ~ r2_hidden(E_57,'#skF_2'(A_7,B_35,k1_connsp_2(A_7,B_35)))
      | ~ m1_subset_1(E_57,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(k1_connsp_2(A_7,B_35),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_subset_1(B_35,u1_struct_0(A_7))
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_144,plain,(
    ! [A_123,B_124] :
      ( v4_pre_topc('#skF_1'(A_123,'#skF_2'(A_123,B_124,k1_connsp_2(A_123,B_124))),A_123)
      | ~ m1_subset_1('#skF_1'(A_123,'#skF_2'(A_123,B_124,k1_connsp_2(A_123,B_124))),k1_zfmisc_1(u1_struct_0(A_123)))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_123),'#skF_2'(A_123,B_124,k1_connsp_2(A_123,B_124))),A_123)
      | ~ m1_subset_1(k1_connsp_2(A_123,B_124),k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_99,c_34])).

tff(c_150,plain,(
    ! [A_125,B_126] :
      ( v4_pre_topc('#skF_1'(A_125,'#skF_2'(A_125,B_126,k1_connsp_2(A_125,B_126))),A_125)
      | ~ m1_subset_1(k1_connsp_2(A_125,B_126),k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | v2_struct_0(A_125)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_125),'#skF_2'(A_125,B_126,k1_connsp_2(A_125,B_126))),A_125)
      | ~ m1_subset_1('#skF_2'(A_125,B_126,k1_connsp_2(A_125,B_126)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125))))
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125) ) ),
    inference(resolution,[status(thm)],[c_6,c_144])).

tff(c_154,plain,(
    ! [A_127,B_128] :
      ( v4_pre_topc('#skF_1'(A_127,'#skF_2'(A_127,B_128,k1_connsp_2(A_127,B_128))),A_127)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_127),'#skF_2'(A_127,B_128,k1_connsp_2(A_127,B_128))),A_127)
      | ~ m1_subset_1(k1_connsp_2(A_127,B_128),k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ m1_subset_1(B_128,u1_struct_0(A_127))
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_28,c_150])).

tff(c_158,plain,(
    ! [A_129,B_130] :
      ( v4_pre_topc('#skF_1'(A_129,'#skF_2'(A_129,B_130,k1_connsp_2(A_129,B_130))),A_129)
      | v4_pre_topc(k1_connsp_2(A_129,B_130),A_129)
      | ~ m1_subset_1(k1_connsp_2(A_129,B_130),k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m1_subset_1(B_130,u1_struct_0(A_129))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129)
      | ~ m1_subset_1(B_130,u1_struct_0(A_129))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_154])).

tff(c_2,plain,(
    ! [A_1,B_5] :
      ( ~ v4_pre_topc('#skF_1'(A_1,B_5),A_1)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_1),B_5),A_1)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_90,plain,(
    ! [A_92,B_93] :
      ( ~ v4_pre_topc('#skF_1'(A_92,'#skF_2'(A_92,B_93,k1_connsp_2(A_92,B_93))),A_92)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_92),'#skF_2'(A_92,B_93,k1_connsp_2(A_92,B_93))),A_92)
      | ~ m1_subset_1(k1_connsp_2(A_92,B_93),k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m1_subset_1(B_93,u1_struct_0(A_92))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_53,c_2])).

tff(c_93,plain,(
    ! [A_60,B_61] :
      ( ~ v4_pre_topc('#skF_1'(A_60,'#skF_2'(A_60,B_61,k1_connsp_2(A_60,B_61))),A_60)
      | v4_pre_topc(k1_connsp_2(A_60,B_61),A_60)
      | ~ m1_subset_1(k1_connsp_2(A_60,B_61),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_90])).

tff(c_166,plain,(
    ! [A_134,B_135] :
      ( v4_pre_topc(k1_connsp_2(A_134,B_135),A_134)
      | ~ m1_subset_1(k1_connsp_2(A_134,B_135),k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m1_subset_1(B_135,u1_struct_0(A_134))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(resolution,[status(thm)],[c_158,c_93])).

tff(c_171,plain,(
    ! [A_136,B_137] :
      ( v4_pre_topc(k1_connsp_2(A_136,B_137),A_136)
      | ~ m1_subset_1(B_137,u1_struct_0(A_136))
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_38,c_166])).

tff(c_40,plain,(
    ~ v4_pre_topc(k1_connsp_2('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_174,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_171,c_40])).

tff(c_177,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_174])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:19:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.42  
% 2.67/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.42  %$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_setfam_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.67/1.42  
% 2.67/1.42  %Foreground sorts:
% 2.67/1.42  
% 2.67/1.42  
% 2.67/1.42  %Background operators:
% 2.67/1.42  
% 2.67/1.42  
% 2.67/1.42  %Foreground operators:
% 2.67/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.67/1.42  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.67/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.42  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 2.67/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.67/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.67/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.67/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.42  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.67/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.42  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.67/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.67/1.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.67/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.67/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.67/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.42  
% 2.67/1.44  tff(f_96, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v4_pre_topc(k1_connsp_2(A, B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_connsp_2)).
% 2.67/1.44  tff(f_83, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 2.67/1.44  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k1_connsp_2(A, B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) & (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(E, D) <=> ((v3_pre_topc(E, A) & v4_pre_topc(E, A)) & r2_hidden(B, E)))))) & (k6_setfam_1(u1_struct_0(A), D) = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_connsp_2)).
% 2.67/1.44  tff(f_41, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v4_pre_topc(C, A)))) => v4_pre_topc(k6_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_pre_topc)).
% 2.67/1.44  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.67/1.44  tff(c_46, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.67/1.44  tff(c_44, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.67/1.44  tff(c_42, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.67/1.44  tff(c_38, plain, (![A_60, B_61]: (m1_subset_1(k1_connsp_2(A_60, B_61), k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.67/1.44  tff(c_60, plain, (![A_73, B_74]: (k6_setfam_1(u1_struct_0(A_73), '#skF_2'(A_73, B_74, k1_connsp_2(A_73, B_74)))=k1_connsp_2(A_73, B_74) | ~m1_subset_1(k1_connsp_2(A_73, B_74), k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(B_74, u1_struct_0(A_73)) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.67/1.44  tff(c_63, plain, (![A_60, B_61]: (k6_setfam_1(u1_struct_0(A_60), '#skF_2'(A_60, B_61, k1_connsp_2(A_60, B_61)))=k1_connsp_2(A_60, B_61) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_38, c_60])).
% 2.67/1.44  tff(c_28, plain, (![A_7, B_35]: (m1_subset_1('#skF_2'(A_7, B_35, k1_connsp_2(A_7, B_35)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7)))) | ~m1_subset_1(k1_connsp_2(A_7, B_35), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_35, u1_struct_0(A_7)) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.67/1.44  tff(c_6, plain, (![A_1, B_5]: (m1_subset_1('#skF_1'(A_1, B_5), k1_zfmisc_1(u1_struct_0(A_1))) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_1), B_5), A_1) | ~m1_subset_1(B_5, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.67/1.44  tff(c_53, plain, (![A_71, B_72]: (m1_subset_1('#skF_2'(A_71, B_72, k1_connsp_2(A_71, B_72)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_71)))) | ~m1_subset_1(k1_connsp_2(A_71, B_72), k1_zfmisc_1(u1_struct_0(A_71))) | ~m1_subset_1(B_72, u1_struct_0(A_71)) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.67/1.44  tff(c_4, plain, (![A_1, B_5]: (r2_hidden('#skF_1'(A_1, B_5), B_5) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_1), B_5), A_1) | ~m1_subset_1(B_5, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.67/1.44  tff(c_99, plain, (![A_99, B_100]: (r2_hidden('#skF_1'(A_99, '#skF_2'(A_99, B_100, k1_connsp_2(A_99, B_100))), '#skF_2'(A_99, B_100, k1_connsp_2(A_99, B_100))) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_99), '#skF_2'(A_99, B_100, k1_connsp_2(A_99, B_100))), A_99) | ~m1_subset_1(k1_connsp_2(A_99, B_100), k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_subset_1(B_100, u1_struct_0(A_99)) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(resolution, [status(thm)], [c_53, c_4])).
% 2.67/1.44  tff(c_34, plain, (![E_57, A_7, B_35]: (v4_pre_topc(E_57, A_7) | ~r2_hidden(E_57, '#skF_2'(A_7, B_35, k1_connsp_2(A_7, B_35))) | ~m1_subset_1(E_57, k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(k1_connsp_2(A_7, B_35), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_subset_1(B_35, u1_struct_0(A_7)) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.67/1.44  tff(c_144, plain, (![A_123, B_124]: (v4_pre_topc('#skF_1'(A_123, '#skF_2'(A_123, B_124, k1_connsp_2(A_123, B_124))), A_123) | ~m1_subset_1('#skF_1'(A_123, '#skF_2'(A_123, B_124, k1_connsp_2(A_123, B_124))), k1_zfmisc_1(u1_struct_0(A_123))) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_123), '#skF_2'(A_123, B_124, k1_connsp_2(A_123, B_124))), A_123) | ~m1_subset_1(k1_connsp_2(A_123, B_124), k1_zfmisc_1(u1_struct_0(A_123))) | ~m1_subset_1(B_124, u1_struct_0(A_123)) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(resolution, [status(thm)], [c_99, c_34])).
% 2.67/1.44  tff(c_150, plain, (![A_125, B_126]: (v4_pre_topc('#skF_1'(A_125, '#skF_2'(A_125, B_126, k1_connsp_2(A_125, B_126))), A_125) | ~m1_subset_1(k1_connsp_2(A_125, B_126), k1_zfmisc_1(u1_struct_0(A_125))) | ~m1_subset_1(B_126, u1_struct_0(A_125)) | v2_struct_0(A_125) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_125), '#skF_2'(A_125, B_126, k1_connsp_2(A_125, B_126))), A_125) | ~m1_subset_1('#skF_2'(A_125, B_126, k1_connsp_2(A_125, B_126)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125)))) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125))), inference(resolution, [status(thm)], [c_6, c_144])).
% 2.67/1.44  tff(c_154, plain, (![A_127, B_128]: (v4_pre_topc('#skF_1'(A_127, '#skF_2'(A_127, B_128, k1_connsp_2(A_127, B_128))), A_127) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_127), '#skF_2'(A_127, B_128, k1_connsp_2(A_127, B_128))), A_127) | ~m1_subset_1(k1_connsp_2(A_127, B_128), k1_zfmisc_1(u1_struct_0(A_127))) | ~m1_subset_1(B_128, u1_struct_0(A_127)) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127) | v2_struct_0(A_127))), inference(resolution, [status(thm)], [c_28, c_150])).
% 2.67/1.44  tff(c_158, plain, (![A_129, B_130]: (v4_pre_topc('#skF_1'(A_129, '#skF_2'(A_129, B_130, k1_connsp_2(A_129, B_130))), A_129) | v4_pre_topc(k1_connsp_2(A_129, B_130), A_129) | ~m1_subset_1(k1_connsp_2(A_129, B_130), k1_zfmisc_1(u1_struct_0(A_129))) | ~m1_subset_1(B_130, u1_struct_0(A_129)) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129) | ~m1_subset_1(B_130, u1_struct_0(A_129)) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129))), inference(superposition, [status(thm), theory('equality')], [c_63, c_154])).
% 2.67/1.44  tff(c_2, plain, (![A_1, B_5]: (~v4_pre_topc('#skF_1'(A_1, B_5), A_1) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_1), B_5), A_1) | ~m1_subset_1(B_5, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.67/1.44  tff(c_90, plain, (![A_92, B_93]: (~v4_pre_topc('#skF_1'(A_92, '#skF_2'(A_92, B_93, k1_connsp_2(A_92, B_93))), A_92) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_92), '#skF_2'(A_92, B_93, k1_connsp_2(A_92, B_93))), A_92) | ~m1_subset_1(k1_connsp_2(A_92, B_93), k1_zfmisc_1(u1_struct_0(A_92))) | ~m1_subset_1(B_93, u1_struct_0(A_92)) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(resolution, [status(thm)], [c_53, c_2])).
% 2.67/1.44  tff(c_93, plain, (![A_60, B_61]: (~v4_pre_topc('#skF_1'(A_60, '#skF_2'(A_60, B_61, k1_connsp_2(A_60, B_61))), A_60) | v4_pre_topc(k1_connsp_2(A_60, B_61), A_60) | ~m1_subset_1(k1_connsp_2(A_60, B_61), k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_63, c_90])).
% 2.67/1.44  tff(c_166, plain, (![A_134, B_135]: (v4_pre_topc(k1_connsp_2(A_134, B_135), A_134) | ~m1_subset_1(k1_connsp_2(A_134, B_135), k1_zfmisc_1(u1_struct_0(A_134))) | ~m1_subset_1(B_135, u1_struct_0(A_134)) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134))), inference(resolution, [status(thm)], [c_158, c_93])).
% 2.67/1.44  tff(c_171, plain, (![A_136, B_137]: (v4_pre_topc(k1_connsp_2(A_136, B_137), A_136) | ~m1_subset_1(B_137, u1_struct_0(A_136)) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(resolution, [status(thm)], [c_38, c_166])).
% 2.67/1.44  tff(c_40, plain, (~v4_pre_topc(k1_connsp_2('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.67/1.44  tff(c_174, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_171, c_40])).
% 2.67/1.44  tff(c_177, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_174])).
% 2.67/1.44  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_177])).
% 2.67/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.44  
% 2.67/1.44  Inference rules
% 2.67/1.44  ----------------------
% 2.67/1.44  #Ref     : 0
% 2.67/1.44  #Sup     : 29
% 2.67/1.44  #Fact    : 0
% 2.67/1.44  #Define  : 0
% 2.67/1.44  #Split   : 0
% 2.67/1.44  #Chain   : 0
% 2.67/1.44  #Close   : 0
% 2.67/1.44  
% 2.67/1.44  Ordering : KBO
% 2.67/1.44  
% 2.67/1.44  Simplification rules
% 2.67/1.44  ----------------------
% 2.67/1.44  #Subsume      : 13
% 2.67/1.44  #Demod        : 3
% 2.67/1.44  #Tautology    : 9
% 2.67/1.44  #SimpNegUnit  : 1
% 2.67/1.44  #BackRed      : 0
% 2.67/1.44  
% 2.67/1.44  #Partial instantiations: 0
% 2.67/1.44  #Strategies tried      : 1
% 2.67/1.44  
% 2.67/1.44  Timing (in seconds)
% 2.67/1.44  ----------------------
% 2.67/1.44  Preprocessing        : 0.35
% 2.67/1.44  Parsing              : 0.17
% 2.67/1.44  CNF conversion       : 0.03
% 2.67/1.44  Main loop            : 0.25
% 2.67/1.44  Inferencing          : 0.11
% 2.67/1.44  Reduction            : 0.06
% 2.67/1.44  Demodulation         : 0.04
% 2.67/1.44  BG Simplification    : 0.02
% 2.67/1.44  Subsumption          : 0.06
% 2.67/1.44  Abstraction          : 0.01
% 2.67/1.44  MUC search           : 0.00
% 2.67/1.44  Cooper               : 0.00
% 2.67/1.44  Total                : 0.63
% 2.67/1.44  Index Insertion      : 0.00
% 2.67/1.44  Index Deletion       : 0.00
% 2.67/1.44  Index Matching       : 0.00
% 2.67/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
