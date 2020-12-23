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
% DateTime   : Thu Dec  3 10:22:44 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.89s
% Verified   : 
% Statistics : Number of formulae       :  146 (1886 expanded)
%              Number of leaves         :   28 ( 638 expanded)
%              Depth                    :   24
%              Number of atoms          :  399 (5944 expanded)
%              Number of equality atoms :    1 (  40 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tops_2 > v1_tops_2 > r2_hidden > m1_subset_1 > l1_pre_topc > k7_setfam_1 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v2_tops_2(B,A)
            <=> v1_tops_2(k7_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_104,axiom,(
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

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k7_setfam_1(A_12,B_13),k1_zfmisc_1(k1_zfmisc_1(A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ v2_tops_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_59,plain,(
    ~ v2_tops_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_46,plain,(
    ! [A_37,B_43] :
      ( m1_subset_1('#skF_3'(A_37,B_43),k1_zfmisc_1(u1_struct_0(A_37)))
      | v2_tops_2(B_43,A_37)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_76,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_3'(A_61,B_62),B_62)
      | v2_tops_2(B_62,A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61))))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_81,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tops_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_76])).

tff(c_85,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_81])).

tff(c_86,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_85])).

tff(c_123,plain,(
    ! [A_79,C_80,B_81] :
      ( r2_hidden(k3_subset_1(A_79,C_80),k7_setfam_1(A_79,B_81))
      | ~ r2_hidden(C_80,B_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(A_79))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k1_zfmisc_1(A_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_70,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(k7_setfam_1(A_54,B_55),k1_zfmisc_1(k1_zfmisc_1(A_54)))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_18,C_20,B_19] :
      ( m1_subset_1(A_18,C_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(C_20))
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_73,plain,(
    ! [A_18,A_54,B_55] :
      ( m1_subset_1(A_18,k1_zfmisc_1(A_54))
      | ~ r2_hidden(A_18,k7_setfam_1(A_54,B_55))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(resolution,[status(thm)],[c_70,c_22])).

tff(c_130,plain,(
    ! [A_82,C_83,B_84] :
      ( m1_subset_1(k3_subset_1(A_82,C_83),k1_zfmisc_1(A_82))
      | ~ r2_hidden(C_83,B_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_82))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k1_zfmisc_1(A_82))) ) ),
    inference(resolution,[status(thm)],[c_123,c_73])).

tff(c_136,plain,(
    ! [A_82] :
      ( m1_subset_1(k3_subset_1(A_82,'#skF_3'('#skF_4','#skF_5')),k1_zfmisc_1(A_82))
      | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),k1_zfmisc_1(A_82))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_82))) ) ),
    inference(resolution,[status(thm)],[c_86,c_130])).

tff(c_18,plain,(
    ! [A_14,C_17,B_15] :
      ( r2_hidden(k3_subset_1(A_14,C_17),k7_setfam_1(A_14,B_15))
      | ~ r2_hidden(C_17,B_15)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_267,plain,(
    ! [A_122,D_123,B_124] :
      ( r2_hidden(k3_subset_1(A_122,D_123),B_124)
      | ~ r2_hidden(D_123,k7_setfam_1(A_122,B_124))
      | ~ m1_subset_1(D_123,k1_zfmisc_1(A_122))
      | ~ m1_subset_1(k7_setfam_1(A_122,B_124),k1_zfmisc_1(k1_zfmisc_1(A_122)))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k1_zfmisc_1(A_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_271,plain,(
    ! [A_125,D_126,B_127] :
      ( r2_hidden(k3_subset_1(A_125,D_126),B_127)
      | ~ r2_hidden(D_126,k7_setfam_1(A_125,B_127))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(A_125))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k1_zfmisc_1(A_125))) ) ),
    inference(resolution,[status(thm)],[c_16,c_267])).

tff(c_285,plain,(
    ! [D_126] :
      ( r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_126),'#skF_5')
      | ~ r2_hidden(D_126,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_48,c_271])).

tff(c_98,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_2'(A_69,B_70),B_70)
      | v1_tops_2(B_70,A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_69))))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_103,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5')
    | v1_tops_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_98])).

tff(c_107,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5')
    | v1_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_103])).

tff(c_108,plain,(
    v1_tops_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_61,plain,(
    ! [A_48,C_49,B_50] :
      ( m1_subset_1(A_48,C_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(C_49))
      | ~ r2_hidden(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_64,plain,(
    ! [A_48] :
      ( m1_subset_1(A_48,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(A_48,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_61])).

tff(c_286,plain,(
    ! [D_128] :
      ( r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_128),'#skF_5')
      | ~ r2_hidden(D_128,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_128,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_48,c_271])).

tff(c_32,plain,(
    ! [C_36,A_27,B_33] :
      ( v3_pre_topc(C_36,A_27)
      | ~ r2_hidden(C_36,B_33)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ v1_tops_2(B_33,A_27)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_27))))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_571,plain,(
    ! [D_160,A_161] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),D_160),A_161)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),D_160),k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ v1_tops_2('#skF_5',A_161)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_161))))
      | ~ l1_pre_topc(A_161)
      | ~ r2_hidden(D_160,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_160,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_286,c_32])).

tff(c_583,plain,(
    ! [D_160] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),D_160),'#skF_4')
      | ~ v1_tops_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden(D_160,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_160,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_160),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_571])).

tff(c_593,plain,(
    ! [D_162] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),D_162),'#skF_4')
      | ~ r2_hidden(D_162,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_162,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_162),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_108,c_583])).

tff(c_24,plain,(
    ! [B_23,A_21] :
      ( v4_pre_topc(B_23,A_21)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_21),B_23),A_21)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_596,plain,(
    ! [D_162] :
      ( v4_pre_topc(D_162,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden(D_162,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_162,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_162),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_593,c_24])).

tff(c_600,plain,(
    ! [D_163] :
      ( v4_pre_topc(D_163,'#skF_4')
      | ~ r2_hidden(D_163,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_163,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_163),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_596])).

tff(c_612,plain,(
    ! [D_164] :
      ( v4_pre_topc(D_164,'#skF_4')
      | ~ r2_hidden(D_164,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_164,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_285,c_600])).

tff(c_636,plain,(
    ! [C_17] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),C_17),'#skF_4')
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),C_17),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(C_17,'#skF_5')
      | ~ m1_subset_1(C_17,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(resolution,[status(thm)],[c_18,c_612])).

tff(c_651,plain,(
    ! [C_165] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),C_165),'#skF_4')
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),C_165),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(C_165,'#skF_5')
      | ~ m1_subset_1(C_165,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_636])).

tff(c_659,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')),'#skF_4')
    | ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_136,c_651])).

tff(c_668,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')),'#skF_4')
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_86,c_659])).

tff(c_670,plain,(
    ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_668])).

tff(c_678,plain,
    ( v2_tops_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_670])).

tff(c_684,plain,(
    v2_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_678])).

tff(c_686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_684])).

tff(c_688,plain,(
    m1_subset_1('#skF_3'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_668])).

tff(c_58,plain,
    ( v2_tops_2('#skF_5','#skF_4')
    | v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_60,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_58])).

tff(c_1162,plain,(
    ! [A_211,A_212,C_213,B_214] :
      ( m1_subset_1(k3_subset_1(A_211,k3_subset_1(A_212,C_213)),k1_zfmisc_1(A_211))
      | ~ m1_subset_1(k3_subset_1(A_212,C_213),k1_zfmisc_1(A_211))
      | ~ m1_subset_1(k7_setfam_1(A_212,B_214),k1_zfmisc_1(k1_zfmisc_1(A_211)))
      | ~ r2_hidden(C_213,B_214)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(A_212))
      | ~ m1_subset_1(B_214,k1_zfmisc_1(k1_zfmisc_1(A_212))) ) ),
    inference(resolution,[status(thm)],[c_18,c_130])).

tff(c_1188,plain,(
    ! [A_217,C_218,B_219] :
      ( m1_subset_1(k3_subset_1(A_217,k3_subset_1(A_217,C_218)),k1_zfmisc_1(A_217))
      | ~ m1_subset_1(k3_subset_1(A_217,C_218),k1_zfmisc_1(A_217))
      | ~ r2_hidden(C_218,B_219)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(A_217))
      | ~ m1_subset_1(B_219,k1_zfmisc_1(k1_zfmisc_1(A_217))) ) ),
    inference(resolution,[status(thm)],[c_16,c_1162])).

tff(c_1222,plain,(
    ! [A_220] :
      ( m1_subset_1(k3_subset_1(A_220,k3_subset_1(A_220,'#skF_3'('#skF_4','#skF_5'))),k1_zfmisc_1(A_220))
      | ~ m1_subset_1(k3_subset_1(A_220,'#skF_3'('#skF_4','#skF_5')),k1_zfmisc_1(A_220))
      | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),k1_zfmisc_1(A_220))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_220))) ) ),
    inference(resolution,[status(thm)],[c_86,c_1188])).

tff(c_298,plain,(
    ! [D_128,A_27] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),D_128),A_27)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),D_128),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ v1_tops_2('#skF_5',A_27)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_27))))
      | ~ l1_pre_topc(A_27)
      | ~ r2_hidden(D_128,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_128,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_286,c_32])).

tff(c_1240,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ v1_tops_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_1222,c_298])).

tff(c_1262,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_688,c_50,c_108,c_1240])).

tff(c_1288,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1262])).

tff(c_1291,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_136,c_1288])).

tff(c_1298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_688,c_1291])).

tff(c_1299,plain,
    ( ~ r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
    | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),k3_subset_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5'))),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1262])).

tff(c_1357,plain,(
    ~ r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1299])).

tff(c_1364,plain,
    ( ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_18,c_1357])).

tff(c_1371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_688,c_86,c_1364])).

tff(c_1373,plain,(
    r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1299])).

tff(c_12,plain,(
    ! [D_11,A_1,B_2] :
      ( r2_hidden(D_11,k7_setfam_1(A_1,B_2))
      | ~ r2_hidden(k3_subset_1(A_1,D_11),B_2)
      | ~ m1_subset_1(D_11,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(k7_setfam_1(A_1,B_2),k1_zfmisc_1(k1_zfmisc_1(A_1)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k1_zfmisc_1(A_1))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1383,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),k7_setfam_1(u1_struct_0('#skF_4'),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')))
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_1373,c_12])).

tff(c_1408,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),k7_setfam_1(u1_struct_0('#skF_4'),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_1383])).

tff(c_1515,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_1408])).

tff(c_1519,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_16,c_1515])).

tff(c_1523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1519])).

tff(c_1525,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_1408])).

tff(c_1300,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1262])).

tff(c_176,plain,(
    ! [C_103,A_104,B_105] :
      ( v3_pre_topc(C_103,A_104)
      | ~ r2_hidden(C_103,B_105)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ v1_tops_2(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_104))))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_181,plain,(
    ! [A_14,C_17,A_104,B_15] :
      ( v3_pre_topc(k3_subset_1(A_14,C_17),A_104)
      | ~ m1_subset_1(k3_subset_1(A_14,C_17),k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ v1_tops_2(k7_setfam_1(A_14,B_15),A_104)
      | ~ m1_subset_1(k7_setfam_1(A_14,B_15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_104))))
      | ~ l1_pre_topc(A_104)
      | ~ r2_hidden(C_17,B_15)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(resolution,[status(thm)],[c_18,c_176])).

tff(c_1311,plain,(
    ! [B_15] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')),'#skF_4')
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),B_15),'#skF_4')
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),B_15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),B_15)
      | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(resolution,[status(thm)],[c_1300,c_181])).

tff(c_1328,plain,(
    ! [B_15] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')),'#skF_4')
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),B_15),'#skF_4')
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),B_15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_50,c_1311])).

tff(c_4238,plain,(
    ! [B_356] :
      ( ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),B_356),'#skF_4')
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),B_356),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),B_356)
      | ~ m1_subset_1(B_356,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(splitLeft,[status(thm)],[c_1328])).

tff(c_4244,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_1525,c_4238])).

tff(c_4255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_86,c_60,c_4244])).

tff(c_4256,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1328])).

tff(c_4259,plain,
    ( v4_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4256,c_24])).

tff(c_4262,plain,(
    v4_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_688,c_4259])).

tff(c_42,plain,(
    ! [A_37,B_43] :
      ( ~ v4_pre_topc('#skF_3'(A_37,B_43),A_37)
      | v2_tops_2(B_43,A_37)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4264,plain,
    ( v2_tops_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4262,c_42])).

tff(c_4267,plain,(
    v2_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4264])).

tff(c_4269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_4267])).

tff(c_4270,plain,(
    ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_4294,plain,(
    ! [A_372,B_373] :
      ( r2_hidden('#skF_2'(A_372,B_373),B_373)
      | v1_tops_2(B_373,A_372)
      | ~ m1_subset_1(B_373,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_372))))
      | ~ l1_pre_topc(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4500,plain,(
    ! [A_441,B_442] :
      ( r2_hidden('#skF_2'(A_441,k7_setfam_1(u1_struct_0(A_441),B_442)),k7_setfam_1(u1_struct_0(A_441),B_442))
      | v1_tops_2(k7_setfam_1(u1_struct_0(A_441),B_442),A_441)
      | ~ l1_pre_topc(A_441)
      | ~ m1_subset_1(B_442,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_441)))) ) ),
    inference(resolution,[status(thm)],[c_16,c_4294])).

tff(c_4283,plain,(
    ! [A_363,B_364] :
      ( m1_subset_1(k7_setfam_1(A_363,B_364),k1_zfmisc_1(k1_zfmisc_1(A_363)))
      | ~ m1_subset_1(B_364,k1_zfmisc_1(k1_zfmisc_1(A_363))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4286,plain,(
    ! [A_18,A_363,B_364] :
      ( m1_subset_1(A_18,k1_zfmisc_1(A_363))
      | ~ r2_hidden(A_18,k7_setfam_1(A_363,B_364))
      | ~ m1_subset_1(B_364,k1_zfmisc_1(k1_zfmisc_1(A_363))) ) ),
    inference(resolution,[status(thm)],[c_4283,c_22])).

tff(c_4527,plain,(
    ! [A_441,B_442] :
      ( m1_subset_1('#skF_2'(A_441,k7_setfam_1(u1_struct_0(A_441),B_442)),k1_zfmisc_1(u1_struct_0(A_441)))
      | v1_tops_2(k7_setfam_1(u1_struct_0(A_441),B_442),A_441)
      | ~ l1_pre_topc(A_441)
      | ~ m1_subset_1(B_442,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_441)))) ) ),
    inference(resolution,[status(thm)],[c_4500,c_4286])).

tff(c_4300,plain,(
    ! [A_372,B_13] :
      ( r2_hidden('#skF_2'(A_372,k7_setfam_1(u1_struct_0(A_372),B_13)),k7_setfam_1(u1_struct_0(A_372),B_13))
      | v1_tops_2(k7_setfam_1(u1_struct_0(A_372),B_13),A_372)
      | ~ l1_pre_topc(A_372)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_372)))) ) ),
    inference(resolution,[status(thm)],[c_16,c_4294])).

tff(c_4397,plain,(
    ! [A_423,D_424,B_425] :
      ( r2_hidden(k3_subset_1(A_423,D_424),B_425)
      | ~ r2_hidden(D_424,k7_setfam_1(A_423,B_425))
      | ~ m1_subset_1(D_424,k1_zfmisc_1(A_423))
      | ~ m1_subset_1(k7_setfam_1(A_423,B_425),k1_zfmisc_1(k1_zfmisc_1(A_423)))
      | ~ m1_subset_1(B_425,k1_zfmisc_1(k1_zfmisc_1(A_423))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4401,plain,(
    ! [A_426,D_427,B_428] :
      ( r2_hidden(k3_subset_1(A_426,D_427),B_428)
      | ~ r2_hidden(D_427,k7_setfam_1(A_426,B_428))
      | ~ m1_subset_1(D_427,k1_zfmisc_1(A_426))
      | ~ m1_subset_1(B_428,k1_zfmisc_1(k1_zfmisc_1(A_426))) ) ),
    inference(resolution,[status(thm)],[c_16,c_4397])).

tff(c_4411,plain,(
    ! [D_427] :
      ( r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_427),'#skF_5')
      | ~ r2_hidden(D_427,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_427,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_48,c_4401])).

tff(c_4271,plain,(
    v2_tops_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_4274,plain,(
    ! [A_357,C_358,B_359] :
      ( m1_subset_1(A_357,C_358)
      | ~ m1_subset_1(B_359,k1_zfmisc_1(C_358))
      | ~ r2_hidden(A_357,B_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4277,plain,(
    ! [A_357] :
      ( m1_subset_1(A_357,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(A_357,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_4274])).

tff(c_4412,plain,(
    ! [D_429] :
      ( r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_429),'#skF_5')
      | ~ r2_hidden(D_429,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_429,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_48,c_4401])).

tff(c_40,plain,(
    ! [C_46,A_37,B_43] :
      ( v4_pre_topc(C_46,A_37)
      | ~ r2_hidden(C_46,B_43)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ v2_tops_2(B_43,A_37)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4547,plain,(
    ! [D_454,A_455] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),D_454),A_455)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),D_454),k1_zfmisc_1(u1_struct_0(A_455)))
      | ~ v2_tops_2('#skF_5',A_455)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_455))))
      | ~ l1_pre_topc(A_455)
      | ~ r2_hidden(D_454,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_454,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_4412,c_40])).

tff(c_4555,plain,(
    ! [D_454] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),D_454),'#skF_4')
      | ~ v2_tops_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden(D_454,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_454,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_454),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4277,c_4547])).

tff(c_4562,plain,(
    ! [D_456] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),D_456),'#skF_4')
      | ~ r2_hidden(D_456,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_456,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_456),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4271,c_4555])).

tff(c_28,plain,(
    ! [B_26,A_24] :
      ( v3_pre_topc(B_26,A_24)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(A_24),B_26),A_24)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4565,plain,(
    ! [D_456] :
      ( v3_pre_topc(D_456,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden(D_456,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_456,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_456),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4562,c_28])).

tff(c_4569,plain,(
    ! [D_457] :
      ( v3_pre_topc(D_457,'#skF_4')
      | ~ r2_hidden(D_457,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_457,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_457),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4565])).

tff(c_4574,plain,(
    ! [D_458] :
      ( v3_pre_topc(D_458,'#skF_4')
      | ~ r2_hidden(D_458,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_458,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_4411,c_4569])).

tff(c_4578,plain,
    ( v3_pre_topc('#skF_2'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),'#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_4300,c_4574])).

tff(c_4593,plain,
    ( v3_pre_topc('#skF_2'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),'#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_4578])).

tff(c_4594,plain,
    ( v3_pre_topc('#skF_2'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),'#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_4270,c_4593])).

tff(c_4604,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_4594])).

tff(c_4607,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_4527,c_4604])).

tff(c_4616,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_4607])).

tff(c_4618,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4270,c_4616])).

tff(c_4619,plain,(
    v3_pre_topc('#skF_2'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_4594])).

tff(c_34,plain,(
    ! [A_27,B_33] :
      ( ~ v3_pre_topc('#skF_2'(A_27,B_33),A_27)
      | v1_tops_2(B_33,A_27)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_27))))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4637,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4619,c_34])).

tff(c_4640,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4637])).

tff(c_4641,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_4270,c_4640])).

tff(c_4644,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_16,c_4641])).

tff(c_4648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4644])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.59/2.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.59  
% 7.59/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.59  %$ v4_pre_topc > v3_pre_topc > v2_tops_2 > v1_tops_2 > r2_hidden > m1_subset_1 > l1_pre_topc > k7_setfam_1 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 7.59/2.59  
% 7.59/2.59  %Foreground sorts:
% 7.59/2.59  
% 7.59/2.59  
% 7.59/2.59  %Background operators:
% 7.59/2.59  
% 7.59/2.59  
% 7.59/2.59  %Foreground operators:
% 7.59/2.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.59/2.59  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.59/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.59/2.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.59/2.59  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 7.59/2.59  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 7.59/2.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.59/2.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.59/2.59  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.59/2.59  tff('#skF_5', type, '#skF_5': $i).
% 7.59/2.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.59/2.59  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 7.59/2.59  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.59/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.59/2.59  tff('#skF_4', type, '#skF_4': $i).
% 7.59/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.59/2.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.59/2.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.59/2.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.59/2.59  
% 7.89/2.61  tff(f_114, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> v1_tops_2(k7_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tops_2)).
% 7.89/2.61  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 7.89/2.61  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_2)).
% 7.89/2.61  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 7.89/2.61  tff(f_58, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 7.89/2.61  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 7.89/2.61  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 7.89/2.61  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 7.89/2.61  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 7.89/2.61  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.89/2.61  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(k7_setfam_1(A_12, B_13), k1_zfmisc_1(k1_zfmisc_1(A_12))) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.89/2.61  tff(c_52, plain, (~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~v2_tops_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.89/2.61  tff(c_59, plain, (~v2_tops_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 7.89/2.61  tff(c_50, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.89/2.61  tff(c_46, plain, (![A_37, B_43]: (m1_subset_1('#skF_3'(A_37, B_43), k1_zfmisc_1(u1_struct_0(A_37))) | v2_tops_2(B_43, A_37) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.89/2.61  tff(c_76, plain, (![A_61, B_62]: (r2_hidden('#skF_3'(A_61, B_62), B_62) | v2_tops_2(B_62, A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61)))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.89/2.61  tff(c_81, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tops_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_48, c_76])).
% 7.89/2.61  tff(c_85, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tops_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_81])).
% 7.89/2.61  tff(c_86, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_59, c_85])).
% 7.89/2.61  tff(c_123, plain, (![A_79, C_80, B_81]: (r2_hidden(k3_subset_1(A_79, C_80), k7_setfam_1(A_79, B_81)) | ~r2_hidden(C_80, B_81) | ~m1_subset_1(C_80, k1_zfmisc_1(A_79)) | ~m1_subset_1(B_81, k1_zfmisc_1(k1_zfmisc_1(A_79))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.89/2.61  tff(c_70, plain, (![A_54, B_55]: (m1_subset_1(k7_setfam_1(A_54, B_55), k1_zfmisc_1(k1_zfmisc_1(A_54))) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_54))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.89/2.61  tff(c_22, plain, (![A_18, C_20, B_19]: (m1_subset_1(A_18, C_20) | ~m1_subset_1(B_19, k1_zfmisc_1(C_20)) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.89/2.61  tff(c_73, plain, (![A_18, A_54, B_55]: (m1_subset_1(A_18, k1_zfmisc_1(A_54)) | ~r2_hidden(A_18, k7_setfam_1(A_54, B_55)) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_54))))), inference(resolution, [status(thm)], [c_70, c_22])).
% 7.89/2.61  tff(c_130, plain, (![A_82, C_83, B_84]: (m1_subset_1(k3_subset_1(A_82, C_83), k1_zfmisc_1(A_82)) | ~r2_hidden(C_83, B_84) | ~m1_subset_1(C_83, k1_zfmisc_1(A_82)) | ~m1_subset_1(B_84, k1_zfmisc_1(k1_zfmisc_1(A_82))))), inference(resolution, [status(thm)], [c_123, c_73])).
% 7.89/2.61  tff(c_136, plain, (![A_82]: (m1_subset_1(k3_subset_1(A_82, '#skF_3'('#skF_4', '#skF_5')), k1_zfmisc_1(A_82)) | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), k1_zfmisc_1(A_82)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_82))))), inference(resolution, [status(thm)], [c_86, c_130])).
% 7.89/2.61  tff(c_18, plain, (![A_14, C_17, B_15]: (r2_hidden(k3_subset_1(A_14, C_17), k7_setfam_1(A_14, B_15)) | ~r2_hidden(C_17, B_15) | ~m1_subset_1(C_17, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.89/2.61  tff(c_267, plain, (![A_122, D_123, B_124]: (r2_hidden(k3_subset_1(A_122, D_123), B_124) | ~r2_hidden(D_123, k7_setfam_1(A_122, B_124)) | ~m1_subset_1(D_123, k1_zfmisc_1(A_122)) | ~m1_subset_1(k7_setfam_1(A_122, B_124), k1_zfmisc_1(k1_zfmisc_1(A_122))) | ~m1_subset_1(B_124, k1_zfmisc_1(k1_zfmisc_1(A_122))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.89/2.61  tff(c_271, plain, (![A_125, D_126, B_127]: (r2_hidden(k3_subset_1(A_125, D_126), B_127) | ~r2_hidden(D_126, k7_setfam_1(A_125, B_127)) | ~m1_subset_1(D_126, k1_zfmisc_1(A_125)) | ~m1_subset_1(B_127, k1_zfmisc_1(k1_zfmisc_1(A_125))))), inference(resolution, [status(thm)], [c_16, c_267])).
% 7.89/2.61  tff(c_285, plain, (![D_126]: (r2_hidden(k3_subset_1(u1_struct_0('#skF_4'), D_126), '#skF_5') | ~r2_hidden(D_126, k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(D_126, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_48, c_271])).
% 7.89/2.61  tff(c_98, plain, (![A_69, B_70]: (r2_hidden('#skF_2'(A_69, B_70), B_70) | v1_tops_2(B_70, A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_69)))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.89/2.61  tff(c_103, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5'), '#skF_5') | v1_tops_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_48, c_98])).
% 7.89/2.61  tff(c_107, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5'), '#skF_5') | v1_tops_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_103])).
% 7.89/2.61  tff(c_108, plain, (v1_tops_2('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_107])).
% 7.89/2.61  tff(c_61, plain, (![A_48, C_49, B_50]: (m1_subset_1(A_48, C_49) | ~m1_subset_1(B_50, k1_zfmisc_1(C_49)) | ~r2_hidden(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.89/2.61  tff(c_64, plain, (![A_48]: (m1_subset_1(A_48, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(A_48, '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_61])).
% 7.89/2.61  tff(c_286, plain, (![D_128]: (r2_hidden(k3_subset_1(u1_struct_0('#skF_4'), D_128), '#skF_5') | ~r2_hidden(D_128, k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(D_128, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_48, c_271])).
% 7.89/2.61  tff(c_32, plain, (![C_36, A_27, B_33]: (v3_pre_topc(C_36, A_27) | ~r2_hidden(C_36, B_33) | ~m1_subset_1(C_36, k1_zfmisc_1(u1_struct_0(A_27))) | ~v1_tops_2(B_33, A_27) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_27)))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.89/2.61  tff(c_571, plain, (![D_160, A_161]: (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), D_160), A_161) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), D_160), k1_zfmisc_1(u1_struct_0(A_161))) | ~v1_tops_2('#skF_5', A_161) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_161)))) | ~l1_pre_topc(A_161) | ~r2_hidden(D_160, k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(D_160, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_286, c_32])).
% 7.89/2.61  tff(c_583, plain, (![D_160]: (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), D_160), '#skF_4') | ~v1_tops_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4') | ~r2_hidden(D_160, k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(D_160, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(k3_subset_1(u1_struct_0('#skF_4'), D_160), '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_571])).
% 7.89/2.61  tff(c_593, plain, (![D_162]: (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), D_162), '#skF_4') | ~r2_hidden(D_162, k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(D_162, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(k3_subset_1(u1_struct_0('#skF_4'), D_162), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_108, c_583])).
% 7.89/2.61  tff(c_24, plain, (![B_23, A_21]: (v4_pre_topc(B_23, A_21) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_21), B_23), A_21) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.89/2.61  tff(c_596, plain, (![D_162]: (v4_pre_topc(D_162, '#skF_4') | ~l1_pre_topc('#skF_4') | ~r2_hidden(D_162, k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(D_162, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(k3_subset_1(u1_struct_0('#skF_4'), D_162), '#skF_5'))), inference(resolution, [status(thm)], [c_593, c_24])).
% 7.89/2.61  tff(c_600, plain, (![D_163]: (v4_pre_topc(D_163, '#skF_4') | ~r2_hidden(D_163, k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(D_163, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(k3_subset_1(u1_struct_0('#skF_4'), D_163), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_596])).
% 7.89/2.61  tff(c_612, plain, (![D_164]: (v4_pre_topc(D_164, '#skF_4') | ~r2_hidden(D_164, k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(D_164, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_285, c_600])).
% 7.89/2.61  tff(c_636, plain, (![C_17]: (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), C_17), '#skF_4') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), C_17), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(C_17, '#skF_5') | ~m1_subset_1(C_17, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(resolution, [status(thm)], [c_18, c_612])).
% 7.89/2.61  tff(c_651, plain, (![C_165]: (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), C_165), '#skF_4') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), C_165), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(C_165, '#skF_5') | ~m1_subset_1(C_165, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_636])).
% 7.89/2.61  tff(c_659, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')), '#skF_4') | ~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_136, c_651])).
% 7.89/2.61  tff(c_668, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')), '#skF_4') | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_86, c_659])).
% 7.89/2.61  tff(c_670, plain, (~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_668])).
% 7.89/2.61  tff(c_678, plain, (v2_tops_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_46, c_670])).
% 7.89/2.61  tff(c_684, plain, (v2_tops_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_678])).
% 7.89/2.61  tff(c_686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_684])).
% 7.89/2.61  tff(c_688, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_668])).
% 7.89/2.61  tff(c_58, plain, (v2_tops_2('#skF_5', '#skF_4') | v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.89/2.61  tff(c_60, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_59, c_58])).
% 7.89/2.61  tff(c_1162, plain, (![A_211, A_212, C_213, B_214]: (m1_subset_1(k3_subset_1(A_211, k3_subset_1(A_212, C_213)), k1_zfmisc_1(A_211)) | ~m1_subset_1(k3_subset_1(A_212, C_213), k1_zfmisc_1(A_211)) | ~m1_subset_1(k7_setfam_1(A_212, B_214), k1_zfmisc_1(k1_zfmisc_1(A_211))) | ~r2_hidden(C_213, B_214) | ~m1_subset_1(C_213, k1_zfmisc_1(A_212)) | ~m1_subset_1(B_214, k1_zfmisc_1(k1_zfmisc_1(A_212))))), inference(resolution, [status(thm)], [c_18, c_130])).
% 7.89/2.61  tff(c_1188, plain, (![A_217, C_218, B_219]: (m1_subset_1(k3_subset_1(A_217, k3_subset_1(A_217, C_218)), k1_zfmisc_1(A_217)) | ~m1_subset_1(k3_subset_1(A_217, C_218), k1_zfmisc_1(A_217)) | ~r2_hidden(C_218, B_219) | ~m1_subset_1(C_218, k1_zfmisc_1(A_217)) | ~m1_subset_1(B_219, k1_zfmisc_1(k1_zfmisc_1(A_217))))), inference(resolution, [status(thm)], [c_16, c_1162])).
% 7.89/2.61  tff(c_1222, plain, (![A_220]: (m1_subset_1(k3_subset_1(A_220, k3_subset_1(A_220, '#skF_3'('#skF_4', '#skF_5'))), k1_zfmisc_1(A_220)) | ~m1_subset_1(k3_subset_1(A_220, '#skF_3'('#skF_4', '#skF_5')), k1_zfmisc_1(A_220)) | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), k1_zfmisc_1(A_220)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_220))))), inference(resolution, [status(thm)], [c_86, c_1188])).
% 7.89/2.61  tff(c_298, plain, (![D_128, A_27]: (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), D_128), A_27) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), D_128), k1_zfmisc_1(u1_struct_0(A_27))) | ~v1_tops_2('#skF_5', A_27) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_27)))) | ~l1_pre_topc(A_27) | ~r2_hidden(D_128, k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(D_128, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_286, c_32])).
% 7.89/2.61  tff(c_1240, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~v1_tops_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r2_hidden(k3_subset_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')), k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1222, c_298])).
% 7.89/2.61  tff(c_1262, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~r2_hidden(k3_subset_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')), k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_688, c_50, c_108, c_1240])).
% 7.89/2.61  tff(c_1288, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_1262])).
% 7.89/2.61  tff(c_1291, plain, (~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_136, c_1288])).
% 7.89/2.61  tff(c_1298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_688, c_1291])).
% 7.89/2.61  tff(c_1299, plain, (~r2_hidden(k3_subset_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')), k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), k3_subset_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5'))), '#skF_4')), inference(splitRight, [status(thm)], [c_1262])).
% 7.89/2.61  tff(c_1357, plain, (~r2_hidden(k3_subset_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')), k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_1299])).
% 7.89/2.61  tff(c_1364, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_18, c_1357])).
% 7.89/2.61  tff(c_1371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_688, c_86, c_1364])).
% 7.89/2.61  tff(c_1373, plain, (r2_hidden(k3_subset_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')), k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'))), inference(splitRight, [status(thm)], [c_1299])).
% 7.89/2.61  tff(c_12, plain, (![D_11, A_1, B_2]: (r2_hidden(D_11, k7_setfam_1(A_1, B_2)) | ~r2_hidden(k3_subset_1(A_1, D_11), B_2) | ~m1_subset_1(D_11, k1_zfmisc_1(A_1)) | ~m1_subset_1(k7_setfam_1(A_1, B_2), k1_zfmisc_1(k1_zfmisc_1(A_1))) | ~m1_subset_1(B_2, k1_zfmisc_1(k1_zfmisc_1(A_1))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.89/2.61  tff(c_1383, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), k7_setfam_1(u1_struct_0('#skF_4'), k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'))) | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'), k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1373, c_12])).
% 7.89/2.61  tff(c_1408, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), k7_setfam_1(u1_struct_0('#skF_4'), k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'))) | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'), k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_688, c_1383])).
% 7.89/2.61  tff(c_1515, plain, (~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_1408])).
% 7.89/2.61  tff(c_1519, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_16, c_1515])).
% 7.89/2.61  tff(c_1523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1519])).
% 7.89/2.61  tff(c_1525, plain, (m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_1408])).
% 7.89/2.61  tff(c_1300, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_1262])).
% 7.89/2.61  tff(c_176, plain, (![C_103, A_104, B_105]: (v3_pre_topc(C_103, A_104) | ~r2_hidden(C_103, B_105) | ~m1_subset_1(C_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~v1_tops_2(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_104)))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.89/2.61  tff(c_181, plain, (![A_14, C_17, A_104, B_15]: (v3_pre_topc(k3_subset_1(A_14, C_17), A_104) | ~m1_subset_1(k3_subset_1(A_14, C_17), k1_zfmisc_1(u1_struct_0(A_104))) | ~v1_tops_2(k7_setfam_1(A_14, B_15), A_104) | ~m1_subset_1(k7_setfam_1(A_14, B_15), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_104)))) | ~l1_pre_topc(A_104) | ~r2_hidden(C_17, B_15) | ~m1_subset_1(C_17, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(resolution, [status(thm)], [c_18, c_176])).
% 7.89/2.61  tff(c_1311, plain, (![B_15]: (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')), '#skF_4') | ~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'), B_15), '#skF_4') | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'), B_15), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4') | ~r2_hidden('#skF_3'('#skF_4', '#skF_5'), B_15) | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(resolution, [status(thm)], [c_1300, c_181])).
% 7.89/2.61  tff(c_1328, plain, (![B_15]: (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')), '#skF_4') | ~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'), B_15), '#skF_4') | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'), B_15), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~r2_hidden('#skF_3'('#skF_4', '#skF_5'), B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_688, c_50, c_1311])).
% 7.89/2.61  tff(c_4238, plain, (![B_356]: (~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'), B_356), '#skF_4') | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'), B_356), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~r2_hidden('#skF_3'('#skF_4', '#skF_5'), B_356) | ~m1_subset_1(B_356, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(splitLeft, [status(thm)], [c_1328])).
% 7.89/2.61  tff(c_4244, plain, (~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1525, c_4238])).
% 7.89/2.61  tff(c_4255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_86, c_60, c_4244])).
% 7.89/2.61  tff(c_4256, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')), '#skF_4')), inference(splitRight, [status(thm)], [c_1328])).
% 7.89/2.61  tff(c_4259, plain, (v4_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4256, c_24])).
% 7.89/2.61  tff(c_4262, plain, (v4_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_688, c_4259])).
% 7.89/2.61  tff(c_42, plain, (![A_37, B_43]: (~v4_pre_topc('#skF_3'(A_37, B_43), A_37) | v2_tops_2(B_43, A_37) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.89/2.61  tff(c_4264, plain, (v2_tops_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4262, c_42])).
% 7.89/2.61  tff(c_4267, plain, (v2_tops_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4264])).
% 7.89/2.61  tff(c_4269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_4267])).
% 7.89/2.61  tff(c_4270, plain, (~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 7.89/2.61  tff(c_4294, plain, (![A_372, B_373]: (r2_hidden('#skF_2'(A_372, B_373), B_373) | v1_tops_2(B_373, A_372) | ~m1_subset_1(B_373, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_372)))) | ~l1_pre_topc(A_372))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.89/2.61  tff(c_4500, plain, (![A_441, B_442]: (r2_hidden('#skF_2'(A_441, k7_setfam_1(u1_struct_0(A_441), B_442)), k7_setfam_1(u1_struct_0(A_441), B_442)) | v1_tops_2(k7_setfam_1(u1_struct_0(A_441), B_442), A_441) | ~l1_pre_topc(A_441) | ~m1_subset_1(B_442, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_441)))))), inference(resolution, [status(thm)], [c_16, c_4294])).
% 7.89/2.61  tff(c_4283, plain, (![A_363, B_364]: (m1_subset_1(k7_setfam_1(A_363, B_364), k1_zfmisc_1(k1_zfmisc_1(A_363))) | ~m1_subset_1(B_364, k1_zfmisc_1(k1_zfmisc_1(A_363))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.89/2.61  tff(c_4286, plain, (![A_18, A_363, B_364]: (m1_subset_1(A_18, k1_zfmisc_1(A_363)) | ~r2_hidden(A_18, k7_setfam_1(A_363, B_364)) | ~m1_subset_1(B_364, k1_zfmisc_1(k1_zfmisc_1(A_363))))), inference(resolution, [status(thm)], [c_4283, c_22])).
% 7.89/2.61  tff(c_4527, plain, (![A_441, B_442]: (m1_subset_1('#skF_2'(A_441, k7_setfam_1(u1_struct_0(A_441), B_442)), k1_zfmisc_1(u1_struct_0(A_441))) | v1_tops_2(k7_setfam_1(u1_struct_0(A_441), B_442), A_441) | ~l1_pre_topc(A_441) | ~m1_subset_1(B_442, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_441)))))), inference(resolution, [status(thm)], [c_4500, c_4286])).
% 7.89/2.61  tff(c_4300, plain, (![A_372, B_13]: (r2_hidden('#skF_2'(A_372, k7_setfam_1(u1_struct_0(A_372), B_13)), k7_setfam_1(u1_struct_0(A_372), B_13)) | v1_tops_2(k7_setfam_1(u1_struct_0(A_372), B_13), A_372) | ~l1_pre_topc(A_372) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_372)))))), inference(resolution, [status(thm)], [c_16, c_4294])).
% 7.89/2.61  tff(c_4397, plain, (![A_423, D_424, B_425]: (r2_hidden(k3_subset_1(A_423, D_424), B_425) | ~r2_hidden(D_424, k7_setfam_1(A_423, B_425)) | ~m1_subset_1(D_424, k1_zfmisc_1(A_423)) | ~m1_subset_1(k7_setfam_1(A_423, B_425), k1_zfmisc_1(k1_zfmisc_1(A_423))) | ~m1_subset_1(B_425, k1_zfmisc_1(k1_zfmisc_1(A_423))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.89/2.61  tff(c_4401, plain, (![A_426, D_427, B_428]: (r2_hidden(k3_subset_1(A_426, D_427), B_428) | ~r2_hidden(D_427, k7_setfam_1(A_426, B_428)) | ~m1_subset_1(D_427, k1_zfmisc_1(A_426)) | ~m1_subset_1(B_428, k1_zfmisc_1(k1_zfmisc_1(A_426))))), inference(resolution, [status(thm)], [c_16, c_4397])).
% 7.89/2.61  tff(c_4411, plain, (![D_427]: (r2_hidden(k3_subset_1(u1_struct_0('#skF_4'), D_427), '#skF_5') | ~r2_hidden(D_427, k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(D_427, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_48, c_4401])).
% 7.89/2.61  tff(c_4271, plain, (v2_tops_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 7.89/2.61  tff(c_4274, plain, (![A_357, C_358, B_359]: (m1_subset_1(A_357, C_358) | ~m1_subset_1(B_359, k1_zfmisc_1(C_358)) | ~r2_hidden(A_357, B_359))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.89/2.61  tff(c_4277, plain, (![A_357]: (m1_subset_1(A_357, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(A_357, '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_4274])).
% 7.89/2.61  tff(c_4412, plain, (![D_429]: (r2_hidden(k3_subset_1(u1_struct_0('#skF_4'), D_429), '#skF_5') | ~r2_hidden(D_429, k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(D_429, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_48, c_4401])).
% 7.89/2.61  tff(c_40, plain, (![C_46, A_37, B_43]: (v4_pre_topc(C_46, A_37) | ~r2_hidden(C_46, B_43) | ~m1_subset_1(C_46, k1_zfmisc_1(u1_struct_0(A_37))) | ~v2_tops_2(B_43, A_37) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.89/2.61  tff(c_4547, plain, (![D_454, A_455]: (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), D_454), A_455) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'), D_454), k1_zfmisc_1(u1_struct_0(A_455))) | ~v2_tops_2('#skF_5', A_455) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_455)))) | ~l1_pre_topc(A_455) | ~r2_hidden(D_454, k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(D_454, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_4412, c_40])).
% 7.89/2.61  tff(c_4555, plain, (![D_454]: (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), D_454), '#skF_4') | ~v2_tops_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4') | ~r2_hidden(D_454, k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(D_454, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(k3_subset_1(u1_struct_0('#skF_4'), D_454), '#skF_5'))), inference(resolution, [status(thm)], [c_4277, c_4547])).
% 7.89/2.61  tff(c_4562, plain, (![D_456]: (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'), D_456), '#skF_4') | ~r2_hidden(D_456, k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(D_456, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(k3_subset_1(u1_struct_0('#skF_4'), D_456), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4271, c_4555])).
% 7.89/2.61  tff(c_28, plain, (![B_26, A_24]: (v3_pre_topc(B_26, A_24) | ~v4_pre_topc(k3_subset_1(u1_struct_0(A_24), B_26), A_24) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.89/2.61  tff(c_4565, plain, (![D_456]: (v3_pre_topc(D_456, '#skF_4') | ~l1_pre_topc('#skF_4') | ~r2_hidden(D_456, k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(D_456, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(k3_subset_1(u1_struct_0('#skF_4'), D_456), '#skF_5'))), inference(resolution, [status(thm)], [c_4562, c_28])).
% 7.89/2.61  tff(c_4569, plain, (![D_457]: (v3_pre_topc(D_457, '#skF_4') | ~r2_hidden(D_457, k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(D_457, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(k3_subset_1(u1_struct_0('#skF_4'), D_457), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4565])).
% 7.89/2.62  tff(c_4574, plain, (![D_458]: (v3_pre_topc(D_458, '#skF_4') | ~r2_hidden(D_458, k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')) | ~m1_subset_1(D_458, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_4411, c_4569])).
% 7.89/2.62  tff(c_4578, plain, (v3_pre_topc('#skF_2'('#skF_4', k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_4300, c_4574])).
% 7.89/2.62  tff(c_4593, plain, (v3_pre_topc('#skF_2'('#skF_4', k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_4578])).
% 7.89/2.62  tff(c_4594, plain, (v3_pre_topc('#skF_2'('#skF_4', k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_4270, c_4593])).
% 7.89/2.62  tff(c_4604, plain, (~m1_subset_1('#skF_2'('#skF_4', k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_4594])).
% 7.89/2.62  tff(c_4607, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_4527, c_4604])).
% 7.89/2.62  tff(c_4616, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_4607])).
% 7.89/2.62  tff(c_4618, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4270, c_4616])).
% 7.89/2.62  tff(c_4619, plain, (v3_pre_topc('#skF_2'('#skF_4', k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5')), '#skF_4')), inference(splitRight, [status(thm)], [c_4594])).
% 7.89/2.62  tff(c_34, plain, (![A_27, B_33]: (~v3_pre_topc('#skF_2'(A_27, B_33), A_27) | v1_tops_2(B_33, A_27) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_27)))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.89/2.62  tff(c_4637, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4619, c_34])).
% 7.89/2.62  tff(c_4640, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), '#skF_4') | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4637])).
% 7.89/2.62  tff(c_4641, plain, (~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'), '#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_4270, c_4640])).
% 7.89/2.62  tff(c_4644, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_16, c_4641])).
% 7.89/2.62  tff(c_4648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_4644])).
% 7.89/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.89/2.62  
% 7.89/2.62  Inference rules
% 7.89/2.62  ----------------------
% 7.89/2.62  #Ref     : 0
% 7.89/2.62  #Sup     : 911
% 7.89/2.62  #Fact    : 2
% 7.89/2.62  #Define  : 0
% 7.89/2.62  #Split   : 23
% 7.89/2.62  #Chain   : 0
% 7.89/2.62  #Close   : 0
% 7.89/2.62  
% 7.89/2.62  Ordering : KBO
% 7.89/2.62  
% 7.89/2.62  Simplification rules
% 7.89/2.62  ----------------------
% 7.89/2.62  #Subsume      : 144
% 7.89/2.62  #Demod        : 614
% 7.89/2.62  #Tautology    : 89
% 7.89/2.62  #SimpNegUnit  : 16
% 7.89/2.62  #BackRed      : 51
% 7.89/2.62  
% 7.89/2.62  #Partial instantiations: 0
% 7.89/2.62  #Strategies tried      : 1
% 7.89/2.62  
% 7.89/2.62  Timing (in seconds)
% 7.89/2.62  ----------------------
% 7.89/2.62  Preprocessing        : 0.32
% 7.89/2.62  Parsing              : 0.17
% 7.89/2.62  CNF conversion       : 0.03
% 7.89/2.62  Main loop            : 1.50
% 7.89/2.62  Inferencing          : 0.45
% 7.89/2.62  Reduction            : 0.41
% 7.89/2.62  Demodulation         : 0.28
% 7.89/2.62  BG Simplification    : 0.06
% 7.89/2.62  Subsumption          : 0.46
% 7.89/2.62  Abstraction          : 0.08
% 7.89/2.62  MUC search           : 0.00
% 7.89/2.62  Cooper               : 0.00
% 7.89/2.62  Total                : 1.87
% 7.89/2.62  Index Insertion      : 0.00
% 7.89/2.62  Index Deletion       : 0.00
% 7.89/2.62  Index Matching       : 0.00
% 7.89/2.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
