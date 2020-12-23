%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1402+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:54 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.72s
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
%$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_setfam_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v4_pre_topc(k1_connsp_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_connsp_2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_55,axiom,(
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

tff(f_82,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_46,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(k1_connsp_2(A_54,B_55),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(B_55,u1_struct_0(A_54))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_60,plain,(
    ! [A_73,B_74] :
      ( k6_setfam_1(u1_struct_0(A_73),'#skF_1'(A_73,B_74,k1_connsp_2(A_73,B_74))) = k1_connsp_2(A_73,B_74)
      | ~ m1_subset_1(k1_connsp_2(A_73,B_74),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_63,plain,(
    ! [A_54,B_55] :
      ( k6_setfam_1(u1_struct_0(A_54),'#skF_1'(A_54,B_55,k1_connsp_2(A_54,B_55))) = k1_connsp_2(A_54,B_55)
      | ~ m1_subset_1(B_55,u1_struct_0(A_54))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_32,c_60])).

tff(c_22,plain,(
    ! [A_1,B_29] :
      ( m1_subset_1('#skF_1'(A_1,B_29,k1_connsp_2(A_1,B_29)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ m1_subset_1(k1_connsp_2(A_1,B_29),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_29,u1_struct_0(A_1))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    ! [A_56,B_60] :
      ( m1_subset_1('#skF_3'(A_56,B_60),k1_zfmisc_1(u1_struct_0(A_56)))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_56),B_60),A_56)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56))))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_53,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1('#skF_1'(A_71,B_72,k1_connsp_2(A_71,B_72)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_71))))
      | ~ m1_subset_1(k1_connsp_2(A_71,B_72),k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ m1_subset_1(B_72,u1_struct_0(A_71))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36,plain,(
    ! [A_56,B_60] :
      ( r2_hidden('#skF_3'(A_56,B_60),B_60)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_56),B_60),A_56)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56))))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_99,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_3'(A_99,'#skF_1'(A_99,B_100,k1_connsp_2(A_99,B_100))),'#skF_1'(A_99,B_100,k1_connsp_2(A_99,B_100)))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_99),'#skF_1'(A_99,B_100,k1_connsp_2(A_99,B_100))),A_99)
      | ~ m1_subset_1(k1_connsp_2(A_99,B_100),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_subset_1(B_100,u1_struct_0(A_99))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_53,c_36])).

tff(c_28,plain,(
    ! [E_51,A_1,B_29] :
      ( v4_pre_topc(E_51,A_1)
      | ~ r2_hidden(E_51,'#skF_1'(A_1,B_29,k1_connsp_2(A_1,B_29)))
      | ~ m1_subset_1(E_51,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(k1_connsp_2(A_1,B_29),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_29,u1_struct_0(A_1))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_144,plain,(
    ! [A_123,B_124] :
      ( v4_pre_topc('#skF_3'(A_123,'#skF_1'(A_123,B_124,k1_connsp_2(A_123,B_124))),A_123)
      | ~ m1_subset_1('#skF_3'(A_123,'#skF_1'(A_123,B_124,k1_connsp_2(A_123,B_124))),k1_zfmisc_1(u1_struct_0(A_123)))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_123),'#skF_1'(A_123,B_124,k1_connsp_2(A_123,B_124))),A_123)
      | ~ m1_subset_1(k1_connsp_2(A_123,B_124),k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_99,c_28])).

tff(c_150,plain,(
    ! [A_125,B_126] :
      ( v4_pre_topc('#skF_3'(A_125,'#skF_1'(A_125,B_126,k1_connsp_2(A_125,B_126))),A_125)
      | ~ m1_subset_1(k1_connsp_2(A_125,B_126),k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | v2_struct_0(A_125)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_125),'#skF_1'(A_125,B_126,k1_connsp_2(A_125,B_126))),A_125)
      | ~ m1_subset_1('#skF_1'(A_125,B_126,k1_connsp_2(A_125,B_126)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125))))
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125) ) ),
    inference(resolution,[status(thm)],[c_38,c_144])).

tff(c_154,plain,(
    ! [A_127,B_128] :
      ( v4_pre_topc('#skF_3'(A_127,'#skF_1'(A_127,B_128,k1_connsp_2(A_127,B_128))),A_127)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_127),'#skF_1'(A_127,B_128,k1_connsp_2(A_127,B_128))),A_127)
      | ~ m1_subset_1(k1_connsp_2(A_127,B_128),k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ m1_subset_1(B_128,u1_struct_0(A_127))
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_22,c_150])).

tff(c_158,plain,(
    ! [A_129,B_130] :
      ( v4_pre_topc('#skF_3'(A_129,'#skF_1'(A_129,B_130,k1_connsp_2(A_129,B_130))),A_129)
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

tff(c_34,plain,(
    ! [A_56,B_60] :
      ( ~ v4_pre_topc('#skF_3'(A_56,B_60),A_56)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_56),B_60),A_56)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56))))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_90,plain,(
    ! [A_92,B_93] :
      ( ~ v4_pre_topc('#skF_3'(A_92,'#skF_1'(A_92,B_93,k1_connsp_2(A_92,B_93))),A_92)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_92),'#skF_1'(A_92,B_93,k1_connsp_2(A_92,B_93))),A_92)
      | ~ m1_subset_1(k1_connsp_2(A_92,B_93),k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m1_subset_1(B_93,u1_struct_0(A_92))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_53,c_34])).

tff(c_93,plain,(
    ! [A_54,B_55] :
      ( ~ v4_pre_topc('#skF_3'(A_54,'#skF_1'(A_54,B_55,k1_connsp_2(A_54,B_55))),A_54)
      | v4_pre_topc(k1_connsp_2(A_54,B_55),A_54)
      | ~ m1_subset_1(k1_connsp_2(A_54,B_55),k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(B_55,u1_struct_0(A_54))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54)
      | ~ m1_subset_1(B_55,u1_struct_0(A_54))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
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
    inference(resolution,[status(thm)],[c_32,c_166])).

tff(c_40,plain,(
    ~ v4_pre_topc(k1_connsp_2('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

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
