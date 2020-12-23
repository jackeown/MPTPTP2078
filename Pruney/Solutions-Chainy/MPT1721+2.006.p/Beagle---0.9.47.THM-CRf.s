%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:44 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 101 expanded)
%              Number of leaves         :   26 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :  263 ( 609 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( ( m1_pre_topc(B,D)
                        & m1_pre_topc(C,D) )
                     => ( r1_tsep_1(B,C)
                        | m1_pre_topc(k2_tsep_1(A,B,C),D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tmap_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k2_tsep_1(A,B,C))
        & v1_pre_topc(k2_tsep_1(A,B,C))
        & m1_pre_topc(k2_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ~ r1_tsep_1(B,C)
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_pre_topc(D)
                      & m1_pre_topc(D,A) )
                   => ( D = k2_tsep_1(A,B,C)
                    <=> u1_struct_0(D) = k3_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_26,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_40,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_30,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_12,plain,(
    ! [A_21,B_22,C_23] :
      ( m1_pre_topc(k2_tsep_1(A_21,B_22,C_23),A_21)
      | ~ m1_pre_topc(C_23,A_21)
      | v2_struct_0(C_23)
      | ~ m1_pre_topc(B_22,A_21)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_49,plain,(
    ! [B_45,A_46] :
      ( l1_pre_topc(B_45)
      | ~ m1_pre_topc(B_45,A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_55,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_49])).

tff(c_68,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_55])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_14,plain,(
    ! [A_21,B_22,C_23] :
      ( v1_pre_topc(k2_tsep_1(A_21,B_22,C_23))
      | ~ m1_pre_topc(C_23,A_21)
      | v2_struct_0(C_23)
      | ~ m1_pre_topc(B_22,A_21)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_151,plain,(
    ! [A_84,B_85,C_86] :
      ( u1_struct_0(k2_tsep_1(A_84,B_85,C_86)) = k3_xboole_0(u1_struct_0(B_85),u1_struct_0(C_86))
      | ~ m1_pre_topc(k2_tsep_1(A_84,B_85,C_86),A_84)
      | ~ v1_pre_topc(k2_tsep_1(A_84,B_85,C_86))
      | v2_struct_0(k2_tsep_1(A_84,B_85,C_86))
      | r1_tsep_1(B_85,C_86)
      | ~ m1_pre_topc(C_86,A_84)
      | v2_struct_0(C_86)
      | ~ m1_pre_topc(B_85,A_84)
      | v2_struct_0(B_85)
      | ~ l1_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_155,plain,(
    ! [A_87,B_88,C_89] :
      ( u1_struct_0(k2_tsep_1(A_87,B_88,C_89)) = k3_xboole_0(u1_struct_0(B_88),u1_struct_0(C_89))
      | ~ v1_pre_topc(k2_tsep_1(A_87,B_88,C_89))
      | v2_struct_0(k2_tsep_1(A_87,B_88,C_89))
      | r1_tsep_1(B_88,C_89)
      | ~ m1_pre_topc(C_89,A_87)
      | v2_struct_0(C_89)
      | ~ m1_pre_topc(B_88,A_87)
      | v2_struct_0(B_88)
      | ~ l1_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_12,c_151])).

tff(c_16,plain,(
    ! [A_21,B_22,C_23] :
      ( ~ v2_struct_0(k2_tsep_1(A_21,B_22,C_23))
      | ~ m1_pre_topc(C_23,A_21)
      | v2_struct_0(C_23)
      | ~ m1_pre_topc(B_22,A_21)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_233,plain,(
    ! [A_93,B_94,C_95] :
      ( u1_struct_0(k2_tsep_1(A_93,B_94,C_95)) = k3_xboole_0(u1_struct_0(B_94),u1_struct_0(C_95))
      | ~ v1_pre_topc(k2_tsep_1(A_93,B_94,C_95))
      | r1_tsep_1(B_94,C_95)
      | ~ m1_pre_topc(C_95,A_93)
      | v2_struct_0(C_95)
      | ~ m1_pre_topc(B_94,A_93)
      | v2_struct_0(B_94)
      | ~ l1_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_155,c_16])).

tff(c_237,plain,(
    ! [A_96,B_97,C_98] :
      ( u1_struct_0(k2_tsep_1(A_96,B_97,C_98)) = k3_xboole_0(u1_struct_0(B_97),u1_struct_0(C_98))
      | r1_tsep_1(B_97,C_98)
      | ~ m1_pre_topc(C_98,A_96)
      | v2_struct_0(C_98)
      | ~ m1_pre_topc(B_97,A_96)
      | v2_struct_0(B_97)
      | ~ l1_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_14,c_233])).

tff(c_86,plain,(
    ! [B_51,A_52] :
      ( m1_subset_1(u1_struct_0(B_51),k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ m1_pre_topc(B_51,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    ! [B_51,A_52] :
      ( r1_tarski(u1_struct_0(B_51),u1_struct_0(A_52))
      | ~ m1_pre_topc(B_51,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_86,c_2])).

tff(c_303,plain,(
    ! [B_99,C_100,A_101,A_102] :
      ( r1_tarski(k3_xboole_0(u1_struct_0(B_99),u1_struct_0(C_100)),u1_struct_0(A_101))
      | ~ m1_pre_topc(k2_tsep_1(A_102,B_99,C_100),A_101)
      | ~ l1_pre_topc(A_101)
      | r1_tsep_1(B_99,C_100)
      | ~ m1_pre_topc(C_100,A_102)
      | v2_struct_0(C_100)
      | ~ m1_pre_topc(B_99,A_102)
      | v2_struct_0(B_99)
      | ~ l1_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_90])).

tff(c_306,plain,(
    ! [B_22,C_23,A_21] :
      ( r1_tarski(k3_xboole_0(u1_struct_0(B_22),u1_struct_0(C_23)),u1_struct_0(A_21))
      | r1_tsep_1(B_22,C_23)
      | ~ m1_pre_topc(C_23,A_21)
      | v2_struct_0(C_23)
      | ~ m1_pre_topc(B_22,A_21)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(resolution,[status(thm)],[c_12,c_303])).

tff(c_22,plain,(
    ! [B_31,C_33,A_27] :
      ( m1_pre_topc(B_31,C_33)
      | ~ r1_tarski(u1_struct_0(B_31),u1_struct_0(C_33))
      | ~ m1_pre_topc(C_33,A_27)
      | ~ m1_pre_topc(B_31,A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_450,plain,(
    ! [A_156,C_152,C_155,A_154,B_153] :
      ( m1_pre_topc(k2_tsep_1(A_154,B_153,C_152),C_155)
      | ~ r1_tarski(k3_xboole_0(u1_struct_0(B_153),u1_struct_0(C_152)),u1_struct_0(C_155))
      | ~ m1_pre_topc(C_155,A_156)
      | ~ m1_pre_topc(k2_tsep_1(A_154,B_153,C_152),A_156)
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | r1_tsep_1(B_153,C_152)
      | ~ m1_pre_topc(C_152,A_154)
      | v2_struct_0(C_152)
      | ~ m1_pre_topc(B_153,A_154)
      | v2_struct_0(B_153)
      | ~ l1_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_22])).

tff(c_761,plain,(
    ! [A_176,B_174,C_173,A_175,A_172] :
      ( m1_pre_topc(k2_tsep_1(A_175,B_174,C_173),A_172)
      | ~ m1_pre_topc(A_172,A_176)
      | ~ m1_pre_topc(k2_tsep_1(A_175,B_174,C_173),A_176)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | ~ m1_pre_topc(C_173,A_175)
      | ~ m1_pre_topc(B_174,A_175)
      | ~ l1_pre_topc(A_175)
      | v2_struct_0(A_175)
      | r1_tsep_1(B_174,C_173)
      | ~ m1_pre_topc(C_173,A_172)
      | v2_struct_0(C_173)
      | ~ m1_pre_topc(B_174,A_172)
      | v2_struct_0(B_174)
      | ~ l1_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_306,c_450])).

tff(c_767,plain,(
    ! [A_175,B_174,C_173] :
      ( m1_pre_topc(k2_tsep_1(A_175,B_174,C_173),'#skF_4')
      | ~ m1_pre_topc(k2_tsep_1(A_175,B_174,C_173),'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc(C_173,A_175)
      | ~ m1_pre_topc(B_174,A_175)
      | ~ l1_pre_topc(A_175)
      | v2_struct_0(A_175)
      | r1_tsep_1(B_174,C_173)
      | ~ m1_pre_topc(C_173,'#skF_4')
      | v2_struct_0(C_173)
      | ~ m1_pre_topc(B_174,'#skF_4')
      | v2_struct_0(B_174)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_761])).

tff(c_781,plain,(
    ! [A_175,B_174,C_173] :
      ( m1_pre_topc(k2_tsep_1(A_175,B_174,C_173),'#skF_4')
      | ~ m1_pre_topc(k2_tsep_1(A_175,B_174,C_173),'#skF_1')
      | ~ m1_pre_topc(C_173,A_175)
      | ~ m1_pre_topc(B_174,A_175)
      | ~ l1_pre_topc(A_175)
      | v2_struct_0(A_175)
      | r1_tsep_1(B_174,C_173)
      | ~ m1_pre_topc(C_173,'#skF_4')
      | v2_struct_0(C_173)
      | ~ m1_pre_topc(B_174,'#skF_4')
      | v2_struct_0(B_174)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_46,c_44,c_767])).

tff(c_795,plain,(
    ! [A_177,B_178,C_179] :
      ( m1_pre_topc(k2_tsep_1(A_177,B_178,C_179),'#skF_4')
      | ~ m1_pre_topc(k2_tsep_1(A_177,B_178,C_179),'#skF_1')
      | ~ m1_pre_topc(C_179,A_177)
      | ~ m1_pre_topc(B_178,A_177)
      | ~ l1_pre_topc(A_177)
      | v2_struct_0(A_177)
      | r1_tsep_1(B_178,C_179)
      | ~ m1_pre_topc(C_179,'#skF_4')
      | v2_struct_0(C_179)
      | ~ m1_pre_topc(B_178,'#skF_4')
      | v2_struct_0(B_178) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_781])).

tff(c_799,plain,(
    ! [B_22,C_23] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_22,C_23),'#skF_4')
      | r1_tsep_1(B_22,C_23)
      | ~ m1_pre_topc(C_23,'#skF_4')
      | ~ m1_pre_topc(B_22,'#skF_4')
      | ~ m1_pre_topc(C_23,'#skF_1')
      | v2_struct_0(C_23)
      | ~ m1_pre_topc(B_22,'#skF_1')
      | v2_struct_0(B_22)
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_12,c_795])).

tff(c_802,plain,(
    ! [B_22,C_23] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_22,C_23),'#skF_4')
      | r1_tsep_1(B_22,C_23)
      | ~ m1_pre_topc(C_23,'#skF_4')
      | ~ m1_pre_topc(B_22,'#skF_4')
      | ~ m1_pre_topc(C_23,'#skF_1')
      | v2_struct_0(C_23)
      | ~ m1_pre_topc(B_22,'#skF_1')
      | v2_struct_0(B_22)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_799])).

tff(c_804,plain,(
    ! [B_180,C_181] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_180,C_181),'#skF_4')
      | r1_tsep_1(B_180,C_181)
      | ~ m1_pre_topc(C_181,'#skF_4')
      | ~ m1_pre_topc(B_180,'#skF_4')
      | ~ m1_pre_topc(C_181,'#skF_1')
      | v2_struct_0(C_181)
      | ~ m1_pre_topc(B_180,'#skF_1')
      | v2_struct_0(B_180) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_802])).

tff(c_24,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_818,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_804,c_24])).

tff(c_838,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_30,c_28,c_818])).

tff(c_840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_38,c_26,c_838])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:26:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.73  
% 4.01/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.73  %$ r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.01/1.73  
% 4.01/1.73  %Foreground sorts:
% 4.01/1.73  
% 4.01/1.73  
% 4.01/1.73  %Background operators:
% 4.01/1.73  
% 4.01/1.73  
% 4.01/1.73  %Foreground operators:
% 4.01/1.73  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.01/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.01/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.01/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.01/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.01/1.73  tff('#skF_1', type, '#skF_1': $i).
% 4.01/1.73  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.01/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.01/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.01/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.73  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.01/1.73  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 4.01/1.73  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.01/1.73  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 4.01/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.01/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.01/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.01/1.73  
% 4.01/1.75  tff(f_145, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, D) & m1_pre_topc(C, D)) => (r1_tsep_1(B, C) | m1_pre_topc(k2_tsep_1(A, B, C), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tmap_1)).
% 4.01/1.75  tff(f_90, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 4.01/1.75  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.01/1.75  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k2_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k3_xboole_0(u1_struct_0(B), u1_struct_0(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tsep_1)).
% 4.01/1.75  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.01/1.75  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.01/1.75  tff(f_111, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 4.01/1.75  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.01/1.75  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.01/1.75  tff(c_26, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.01/1.75  tff(c_40, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.01/1.75  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.01/1.75  tff(c_30, plain, (m1_pre_topc('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.01/1.75  tff(c_28, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.01/1.75  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.01/1.75  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.01/1.75  tff(c_12, plain, (![A_21, B_22, C_23]: (m1_pre_topc(k2_tsep_1(A_21, B_22, C_23), A_21) | ~m1_pre_topc(C_23, A_21) | v2_struct_0(C_23) | ~m1_pre_topc(B_22, A_21) | v2_struct_0(B_22) | ~l1_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.01/1.75  tff(c_34, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.01/1.75  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.01/1.75  tff(c_49, plain, (![B_45, A_46]: (l1_pre_topc(B_45) | ~m1_pre_topc(B_45, A_46) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.01/1.75  tff(c_55, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_49])).
% 4.01/1.75  tff(c_68, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_55])).
% 4.01/1.75  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.01/1.75  tff(c_14, plain, (![A_21, B_22, C_23]: (v1_pre_topc(k2_tsep_1(A_21, B_22, C_23)) | ~m1_pre_topc(C_23, A_21) | v2_struct_0(C_23) | ~m1_pre_topc(B_22, A_21) | v2_struct_0(B_22) | ~l1_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.01/1.75  tff(c_151, plain, (![A_84, B_85, C_86]: (u1_struct_0(k2_tsep_1(A_84, B_85, C_86))=k3_xboole_0(u1_struct_0(B_85), u1_struct_0(C_86)) | ~m1_pre_topc(k2_tsep_1(A_84, B_85, C_86), A_84) | ~v1_pre_topc(k2_tsep_1(A_84, B_85, C_86)) | v2_struct_0(k2_tsep_1(A_84, B_85, C_86)) | r1_tsep_1(B_85, C_86) | ~m1_pre_topc(C_86, A_84) | v2_struct_0(C_86) | ~m1_pre_topc(B_85, A_84) | v2_struct_0(B_85) | ~l1_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.01/1.75  tff(c_155, plain, (![A_87, B_88, C_89]: (u1_struct_0(k2_tsep_1(A_87, B_88, C_89))=k3_xboole_0(u1_struct_0(B_88), u1_struct_0(C_89)) | ~v1_pre_topc(k2_tsep_1(A_87, B_88, C_89)) | v2_struct_0(k2_tsep_1(A_87, B_88, C_89)) | r1_tsep_1(B_88, C_89) | ~m1_pre_topc(C_89, A_87) | v2_struct_0(C_89) | ~m1_pre_topc(B_88, A_87) | v2_struct_0(B_88) | ~l1_pre_topc(A_87) | v2_struct_0(A_87))), inference(resolution, [status(thm)], [c_12, c_151])).
% 4.01/1.75  tff(c_16, plain, (![A_21, B_22, C_23]: (~v2_struct_0(k2_tsep_1(A_21, B_22, C_23)) | ~m1_pre_topc(C_23, A_21) | v2_struct_0(C_23) | ~m1_pre_topc(B_22, A_21) | v2_struct_0(B_22) | ~l1_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.01/1.75  tff(c_233, plain, (![A_93, B_94, C_95]: (u1_struct_0(k2_tsep_1(A_93, B_94, C_95))=k3_xboole_0(u1_struct_0(B_94), u1_struct_0(C_95)) | ~v1_pre_topc(k2_tsep_1(A_93, B_94, C_95)) | r1_tsep_1(B_94, C_95) | ~m1_pre_topc(C_95, A_93) | v2_struct_0(C_95) | ~m1_pre_topc(B_94, A_93) | v2_struct_0(B_94) | ~l1_pre_topc(A_93) | v2_struct_0(A_93))), inference(resolution, [status(thm)], [c_155, c_16])).
% 4.01/1.75  tff(c_237, plain, (![A_96, B_97, C_98]: (u1_struct_0(k2_tsep_1(A_96, B_97, C_98))=k3_xboole_0(u1_struct_0(B_97), u1_struct_0(C_98)) | r1_tsep_1(B_97, C_98) | ~m1_pre_topc(C_98, A_96) | v2_struct_0(C_98) | ~m1_pre_topc(B_97, A_96) | v2_struct_0(B_97) | ~l1_pre_topc(A_96) | v2_struct_0(A_96))), inference(resolution, [status(thm)], [c_14, c_233])).
% 4.01/1.75  tff(c_86, plain, (![B_51, A_52]: (m1_subset_1(u1_struct_0(B_51), k1_zfmisc_1(u1_struct_0(A_52))) | ~m1_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.01/1.75  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.01/1.75  tff(c_90, plain, (![B_51, A_52]: (r1_tarski(u1_struct_0(B_51), u1_struct_0(A_52)) | ~m1_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_86, c_2])).
% 4.01/1.75  tff(c_303, plain, (![B_99, C_100, A_101, A_102]: (r1_tarski(k3_xboole_0(u1_struct_0(B_99), u1_struct_0(C_100)), u1_struct_0(A_101)) | ~m1_pre_topc(k2_tsep_1(A_102, B_99, C_100), A_101) | ~l1_pre_topc(A_101) | r1_tsep_1(B_99, C_100) | ~m1_pre_topc(C_100, A_102) | v2_struct_0(C_100) | ~m1_pre_topc(B_99, A_102) | v2_struct_0(B_99) | ~l1_pre_topc(A_102) | v2_struct_0(A_102))), inference(superposition, [status(thm), theory('equality')], [c_237, c_90])).
% 4.01/1.75  tff(c_306, plain, (![B_22, C_23, A_21]: (r1_tarski(k3_xboole_0(u1_struct_0(B_22), u1_struct_0(C_23)), u1_struct_0(A_21)) | r1_tsep_1(B_22, C_23) | ~m1_pre_topc(C_23, A_21) | v2_struct_0(C_23) | ~m1_pre_topc(B_22, A_21) | v2_struct_0(B_22) | ~l1_pre_topc(A_21) | v2_struct_0(A_21))), inference(resolution, [status(thm)], [c_12, c_303])).
% 4.01/1.75  tff(c_22, plain, (![B_31, C_33, A_27]: (m1_pre_topc(B_31, C_33) | ~r1_tarski(u1_struct_0(B_31), u1_struct_0(C_33)) | ~m1_pre_topc(C_33, A_27) | ~m1_pre_topc(B_31, A_27) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.01/1.75  tff(c_450, plain, (![A_156, C_152, C_155, A_154, B_153]: (m1_pre_topc(k2_tsep_1(A_154, B_153, C_152), C_155) | ~r1_tarski(k3_xboole_0(u1_struct_0(B_153), u1_struct_0(C_152)), u1_struct_0(C_155)) | ~m1_pre_topc(C_155, A_156) | ~m1_pre_topc(k2_tsep_1(A_154, B_153, C_152), A_156) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | r1_tsep_1(B_153, C_152) | ~m1_pre_topc(C_152, A_154) | v2_struct_0(C_152) | ~m1_pre_topc(B_153, A_154) | v2_struct_0(B_153) | ~l1_pre_topc(A_154) | v2_struct_0(A_154))), inference(superposition, [status(thm), theory('equality')], [c_237, c_22])).
% 4.01/1.75  tff(c_761, plain, (![A_176, B_174, C_173, A_175, A_172]: (m1_pre_topc(k2_tsep_1(A_175, B_174, C_173), A_172) | ~m1_pre_topc(A_172, A_176) | ~m1_pre_topc(k2_tsep_1(A_175, B_174, C_173), A_176) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | ~m1_pre_topc(C_173, A_175) | ~m1_pre_topc(B_174, A_175) | ~l1_pre_topc(A_175) | v2_struct_0(A_175) | r1_tsep_1(B_174, C_173) | ~m1_pre_topc(C_173, A_172) | v2_struct_0(C_173) | ~m1_pre_topc(B_174, A_172) | v2_struct_0(B_174) | ~l1_pre_topc(A_172) | v2_struct_0(A_172))), inference(resolution, [status(thm)], [c_306, c_450])).
% 4.01/1.75  tff(c_767, plain, (![A_175, B_174, C_173]: (m1_pre_topc(k2_tsep_1(A_175, B_174, C_173), '#skF_4') | ~m1_pre_topc(k2_tsep_1(A_175, B_174, C_173), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc(C_173, A_175) | ~m1_pre_topc(B_174, A_175) | ~l1_pre_topc(A_175) | v2_struct_0(A_175) | r1_tsep_1(B_174, C_173) | ~m1_pre_topc(C_173, '#skF_4') | v2_struct_0(C_173) | ~m1_pre_topc(B_174, '#skF_4') | v2_struct_0(B_174) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_761])).
% 4.01/1.75  tff(c_781, plain, (![A_175, B_174, C_173]: (m1_pre_topc(k2_tsep_1(A_175, B_174, C_173), '#skF_4') | ~m1_pre_topc(k2_tsep_1(A_175, B_174, C_173), '#skF_1') | ~m1_pre_topc(C_173, A_175) | ~m1_pre_topc(B_174, A_175) | ~l1_pre_topc(A_175) | v2_struct_0(A_175) | r1_tsep_1(B_174, C_173) | ~m1_pre_topc(C_173, '#skF_4') | v2_struct_0(C_173) | ~m1_pre_topc(B_174, '#skF_4') | v2_struct_0(B_174) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_46, c_44, c_767])).
% 4.01/1.75  tff(c_795, plain, (![A_177, B_178, C_179]: (m1_pre_topc(k2_tsep_1(A_177, B_178, C_179), '#skF_4') | ~m1_pre_topc(k2_tsep_1(A_177, B_178, C_179), '#skF_1') | ~m1_pre_topc(C_179, A_177) | ~m1_pre_topc(B_178, A_177) | ~l1_pre_topc(A_177) | v2_struct_0(A_177) | r1_tsep_1(B_178, C_179) | ~m1_pre_topc(C_179, '#skF_4') | v2_struct_0(C_179) | ~m1_pre_topc(B_178, '#skF_4') | v2_struct_0(B_178))), inference(negUnitSimplification, [status(thm)], [c_34, c_781])).
% 4.01/1.75  tff(c_799, plain, (![B_22, C_23]: (m1_pre_topc(k2_tsep_1('#skF_1', B_22, C_23), '#skF_4') | r1_tsep_1(B_22, C_23) | ~m1_pre_topc(C_23, '#skF_4') | ~m1_pre_topc(B_22, '#skF_4') | ~m1_pre_topc(C_23, '#skF_1') | v2_struct_0(C_23) | ~m1_pre_topc(B_22, '#skF_1') | v2_struct_0(B_22) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_795])).
% 4.01/1.75  tff(c_802, plain, (![B_22, C_23]: (m1_pre_topc(k2_tsep_1('#skF_1', B_22, C_23), '#skF_4') | r1_tsep_1(B_22, C_23) | ~m1_pre_topc(C_23, '#skF_4') | ~m1_pre_topc(B_22, '#skF_4') | ~m1_pre_topc(C_23, '#skF_1') | v2_struct_0(C_23) | ~m1_pre_topc(B_22, '#skF_1') | v2_struct_0(B_22) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_799])).
% 4.01/1.75  tff(c_804, plain, (![B_180, C_181]: (m1_pre_topc(k2_tsep_1('#skF_1', B_180, C_181), '#skF_4') | r1_tsep_1(B_180, C_181) | ~m1_pre_topc(C_181, '#skF_4') | ~m1_pre_topc(B_180, '#skF_4') | ~m1_pre_topc(C_181, '#skF_1') | v2_struct_0(C_181) | ~m1_pre_topc(B_180, '#skF_1') | v2_struct_0(B_180))), inference(negUnitSimplification, [status(thm)], [c_48, c_802])).
% 4.01/1.75  tff(c_24, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.01/1.75  tff(c_818, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_804, c_24])).
% 4.01/1.75  tff(c_838, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_30, c_28, c_818])).
% 4.01/1.75  tff(c_840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_38, c_26, c_838])).
% 4.01/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.75  
% 4.01/1.75  Inference rules
% 4.01/1.75  ----------------------
% 4.01/1.75  #Ref     : 0
% 4.01/1.75  #Sup     : 232
% 4.01/1.75  #Fact    : 0
% 4.01/1.75  #Define  : 0
% 4.01/1.75  #Split   : 1
% 4.01/1.75  #Chain   : 0
% 4.01/1.75  #Close   : 0
% 4.01/1.75  
% 4.01/1.75  Ordering : KBO
% 4.01/1.75  
% 4.01/1.75  Simplification rules
% 4.01/1.75  ----------------------
% 4.01/1.75  #Subsume      : 47
% 4.01/1.75  #Demod        : 44
% 4.01/1.75  #Tautology    : 12
% 4.01/1.75  #SimpNegUnit  : 13
% 4.01/1.75  #BackRed      : 0
% 4.01/1.75  
% 4.01/1.75  #Partial instantiations: 0
% 4.01/1.75  #Strategies tried      : 1
% 4.01/1.75  
% 4.01/1.75  Timing (in seconds)
% 4.01/1.75  ----------------------
% 4.01/1.75  Preprocessing        : 0.33
% 4.01/1.75  Parsing              : 0.18
% 4.01/1.75  CNF conversion       : 0.03
% 4.01/1.75  Main loop            : 0.59
% 4.01/1.75  Inferencing          : 0.22
% 4.01/1.75  Reduction            : 0.14
% 4.01/1.75  Demodulation         : 0.09
% 4.01/1.75  BG Simplification    : 0.03
% 4.01/1.75  Subsumption          : 0.17
% 4.01/1.75  Abstraction          : 0.03
% 4.01/1.75  MUC search           : 0.00
% 4.01/1.75  Cooper               : 0.00
% 4.01/1.75  Total                : 0.95
% 4.01/1.75  Index Insertion      : 0.00
% 4.01/1.75  Index Deletion       : 0.00
% 4.01/1.75  Index Matching       : 0.00
% 4.01/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
