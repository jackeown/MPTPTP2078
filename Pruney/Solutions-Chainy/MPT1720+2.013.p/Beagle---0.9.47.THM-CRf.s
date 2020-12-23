%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:43 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 110 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  235 ( 627 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
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
                   => ( ( m1_pre_topc(B,C)
                        & m1_pre_topc(D,C) )
                     => m1_pre_topc(k1_tsep_1(A,B,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_pre_topc(D)
                    & m1_pre_topc(D,A) )
                 => ( D = k1_tsep_1(A,B,C)
                  <=> u1_struct_0(D) = k2_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_108,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_38,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_12,plain,(
    ! [A_21,B_22,C_23] :
      ( m1_pre_topc(k1_tsep_1(A_21,B_22,C_23),A_21)
      | ~ m1_pre_topc(C_23,A_21)
      | v2_struct_0(C_23)
      | ~ m1_pre_topc(B_22,A_21)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_26,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_47,plain,(
    ! [B_45,A_46] :
      ( l1_pre_topc(B_45)
      | ~ m1_pre_topc(B_45,A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_62,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_47])).

tff(c_73,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_62])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_14,plain,(
    ! [A_21,B_22,C_23] :
      ( v1_pre_topc(k1_tsep_1(A_21,B_22,C_23))
      | ~ m1_pre_topc(C_23,A_21)
      | v2_struct_0(C_23)
      | ~ m1_pre_topc(B_22,A_21)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_145,plain,(
    ! [A_80,B_81,C_82] :
      ( u1_struct_0(k1_tsep_1(A_80,B_81,C_82)) = k2_xboole_0(u1_struct_0(B_81),u1_struct_0(C_82))
      | ~ m1_pre_topc(k1_tsep_1(A_80,B_81,C_82),A_80)
      | ~ v1_pre_topc(k1_tsep_1(A_80,B_81,C_82))
      | v2_struct_0(k1_tsep_1(A_80,B_81,C_82))
      | ~ m1_pre_topc(C_82,A_80)
      | v2_struct_0(C_82)
      | ~ m1_pre_topc(B_81,A_80)
      | v2_struct_0(B_81)
      | ~ l1_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_153,plain,(
    ! [A_87,B_88,C_89] :
      ( u1_struct_0(k1_tsep_1(A_87,B_88,C_89)) = k2_xboole_0(u1_struct_0(B_88),u1_struct_0(C_89))
      | ~ v1_pre_topc(k1_tsep_1(A_87,B_88,C_89))
      | v2_struct_0(k1_tsep_1(A_87,B_88,C_89))
      | ~ m1_pre_topc(C_89,A_87)
      | v2_struct_0(C_89)
      | ~ m1_pre_topc(B_88,A_87)
      | v2_struct_0(B_88)
      | ~ l1_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_12,c_145])).

tff(c_16,plain,(
    ! [A_21,B_22,C_23] :
      ( ~ v2_struct_0(k1_tsep_1(A_21,B_22,C_23))
      | ~ m1_pre_topc(C_23,A_21)
      | v2_struct_0(C_23)
      | ~ m1_pre_topc(B_22,A_21)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_223,plain,(
    ! [A_90,B_91,C_92] :
      ( u1_struct_0(k1_tsep_1(A_90,B_91,C_92)) = k2_xboole_0(u1_struct_0(B_91),u1_struct_0(C_92))
      | ~ v1_pre_topc(k1_tsep_1(A_90,B_91,C_92))
      | ~ m1_pre_topc(C_92,A_90)
      | v2_struct_0(C_92)
      | ~ m1_pre_topc(B_91,A_90)
      | v2_struct_0(B_91)
      | ~ l1_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_153,c_16])).

tff(c_235,plain,(
    ! [A_96,B_97,C_98] :
      ( u1_struct_0(k1_tsep_1(A_96,B_97,C_98)) = k2_xboole_0(u1_struct_0(B_97),u1_struct_0(C_98))
      | ~ m1_pre_topc(C_98,A_96)
      | v2_struct_0(C_98)
      | ~ m1_pre_topc(B_97,A_96)
      | v2_struct_0(B_97)
      | ~ l1_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_14,c_223])).

tff(c_84,plain,(
    ! [B_51,A_52] :
      ( m1_subset_1(u1_struct_0(B_51),k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ m1_pre_topc(B_51,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    ! [B_51,A_52] :
      ( r1_tarski(u1_struct_0(B_51),u1_struct_0(A_52))
      | ~ m1_pre_topc(B_51,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_301,plain,(
    ! [B_99,C_100,A_101,A_102] :
      ( r1_tarski(k2_xboole_0(u1_struct_0(B_99),u1_struct_0(C_100)),u1_struct_0(A_101))
      | ~ m1_pre_topc(k1_tsep_1(A_102,B_99,C_100),A_101)
      | ~ l1_pre_topc(A_101)
      | ~ m1_pre_topc(C_100,A_102)
      | v2_struct_0(C_100)
      | ~ m1_pre_topc(B_99,A_102)
      | v2_struct_0(B_99)
      | ~ l1_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_88])).

tff(c_304,plain,(
    ! [B_22,C_23,A_21] :
      ( r1_tarski(k2_xboole_0(u1_struct_0(B_22),u1_struct_0(C_23)),u1_struct_0(A_21))
      | ~ m1_pre_topc(C_23,A_21)
      | v2_struct_0(C_23)
      | ~ m1_pre_topc(B_22,A_21)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(resolution,[status(thm)],[c_12,c_301])).

tff(c_22,plain,(
    ! [B_31,C_33,A_27] :
      ( m1_pre_topc(B_31,C_33)
      | ~ r1_tarski(u1_struct_0(B_31),u1_struct_0(C_33))
      | ~ m1_pre_topc(C_33,A_27)
      | ~ m1_pre_topc(B_31,A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_692,plain,(
    ! [A_163,C_162,C_159,A_161,B_160] :
      ( m1_pre_topc(k1_tsep_1(A_161,B_160,C_159),C_162)
      | ~ r1_tarski(k2_xboole_0(u1_struct_0(B_160),u1_struct_0(C_159)),u1_struct_0(C_162))
      | ~ m1_pre_topc(C_162,A_163)
      | ~ m1_pre_topc(k1_tsep_1(A_161,B_160,C_159),A_163)
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | ~ m1_pre_topc(C_159,A_161)
      | v2_struct_0(C_159)
      | ~ m1_pre_topc(B_160,A_161)
      | v2_struct_0(B_160)
      | ~ l1_pre_topc(A_161)
      | v2_struct_0(A_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_22])).

tff(c_746,plain,(
    ! [C_170,A_171,A_169,A_172,B_173] :
      ( m1_pre_topc(k1_tsep_1(A_171,B_173,C_170),A_169)
      | ~ m1_pre_topc(A_169,A_172)
      | ~ m1_pre_topc(k1_tsep_1(A_171,B_173,C_170),A_172)
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | ~ m1_pre_topc(C_170,A_171)
      | ~ m1_pre_topc(B_173,A_171)
      | ~ l1_pre_topc(A_171)
      | v2_struct_0(A_171)
      | ~ m1_pre_topc(C_170,A_169)
      | v2_struct_0(C_170)
      | ~ m1_pre_topc(B_173,A_169)
      | v2_struct_0(B_173)
      | ~ l1_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(resolution,[status(thm)],[c_304,c_692])).

tff(c_758,plain,(
    ! [A_171,B_173,C_170] :
      ( m1_pre_topc(k1_tsep_1(A_171,B_173,C_170),'#skF_3')
      | ~ m1_pre_topc(k1_tsep_1(A_171,B_173,C_170),'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc(C_170,A_171)
      | ~ m1_pre_topc(B_173,A_171)
      | ~ l1_pre_topc(A_171)
      | v2_struct_0(A_171)
      | ~ m1_pre_topc(C_170,'#skF_3')
      | v2_struct_0(C_170)
      | ~ m1_pre_topc(B_173,'#skF_3')
      | v2_struct_0(B_173)
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_746])).

tff(c_778,plain,(
    ! [A_171,B_173,C_170] :
      ( m1_pre_topc(k1_tsep_1(A_171,B_173,C_170),'#skF_3')
      | ~ m1_pre_topc(k1_tsep_1(A_171,B_173,C_170),'#skF_1')
      | ~ m1_pre_topc(C_170,A_171)
      | ~ m1_pre_topc(B_173,A_171)
      | ~ l1_pre_topc(A_171)
      | v2_struct_0(A_171)
      | ~ m1_pre_topc(C_170,'#skF_3')
      | v2_struct_0(C_170)
      | ~ m1_pre_topc(B_173,'#skF_3')
      | v2_struct_0(B_173)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_44,c_42,c_758])).

tff(c_870,plain,(
    ! [A_185,B_186,C_187] :
      ( m1_pre_topc(k1_tsep_1(A_185,B_186,C_187),'#skF_3')
      | ~ m1_pre_topc(k1_tsep_1(A_185,B_186,C_187),'#skF_1')
      | ~ m1_pre_topc(C_187,A_185)
      | ~ m1_pre_topc(B_186,A_185)
      | ~ l1_pre_topc(A_185)
      | v2_struct_0(A_185)
      | ~ m1_pre_topc(C_187,'#skF_3')
      | v2_struct_0(C_187)
      | ~ m1_pre_topc(B_186,'#skF_3')
      | v2_struct_0(B_186) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_778])).

tff(c_24,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_886,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_870,c_24])).

tff(c_905,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_42,c_38,c_30,c_886])).

tff(c_906,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_32,c_46,c_905])).

tff(c_909,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_906])).

tff(c_912,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_30,c_909])).

tff(c_914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_32,c_912])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 21:01:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.94/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.69  
% 3.94/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.69  %$ r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.94/1.69  
% 3.94/1.69  %Foreground sorts:
% 3.94/1.69  
% 3.94/1.69  
% 3.94/1.69  %Background operators:
% 3.94/1.69  
% 3.94/1.69  
% 3.94/1.69  %Foreground operators:
% 3.94/1.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.94/1.69  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 3.94/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.94/1.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.94/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.94/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.94/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.94/1.69  tff('#skF_1', type, '#skF_1': $i).
% 3.94/1.69  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.94/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.94/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.94/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.94/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.94/1.69  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.94/1.69  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.94/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.94/1.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.94/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.94/1.69  
% 3.94/1.71  tff(f_140, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, C) & m1_pre_topc(D, C)) => m1_pre_topc(k1_tsep_1(A, B, D), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tmap_1)).
% 3.94/1.71  tff(f_87, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 3.94/1.71  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.94/1.71  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k1_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k2_xboole_0(u1_struct_0(B), u1_struct_0(C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tsep_1)).
% 3.94/1.71  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.94/1.71  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.94/1.71  tff(f_108, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 3.94/1.71  tff(c_46, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.94/1.71  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.94/1.71  tff(c_32, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.94/1.71  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.94/1.71  tff(c_38, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.94/1.71  tff(c_30, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.94/1.71  tff(c_12, plain, (![A_21, B_22, C_23]: (m1_pre_topc(k1_tsep_1(A_21, B_22, C_23), A_21) | ~m1_pre_topc(C_23, A_21) | v2_struct_0(C_23) | ~m1_pre_topc(B_22, A_21) | v2_struct_0(B_22) | ~l1_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.94/1.71  tff(c_28, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.94/1.71  tff(c_26, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.94/1.71  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.94/1.71  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.94/1.71  tff(c_47, plain, (![B_45, A_46]: (l1_pre_topc(B_45) | ~m1_pre_topc(B_45, A_46) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.94/1.71  tff(c_62, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_47])).
% 3.94/1.71  tff(c_73, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_62])).
% 3.94/1.71  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.94/1.71  tff(c_14, plain, (![A_21, B_22, C_23]: (v1_pre_topc(k1_tsep_1(A_21, B_22, C_23)) | ~m1_pre_topc(C_23, A_21) | v2_struct_0(C_23) | ~m1_pre_topc(B_22, A_21) | v2_struct_0(B_22) | ~l1_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.94/1.71  tff(c_145, plain, (![A_80, B_81, C_82]: (u1_struct_0(k1_tsep_1(A_80, B_81, C_82))=k2_xboole_0(u1_struct_0(B_81), u1_struct_0(C_82)) | ~m1_pre_topc(k1_tsep_1(A_80, B_81, C_82), A_80) | ~v1_pre_topc(k1_tsep_1(A_80, B_81, C_82)) | v2_struct_0(k1_tsep_1(A_80, B_81, C_82)) | ~m1_pre_topc(C_82, A_80) | v2_struct_0(C_82) | ~m1_pre_topc(B_81, A_80) | v2_struct_0(B_81) | ~l1_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.94/1.71  tff(c_153, plain, (![A_87, B_88, C_89]: (u1_struct_0(k1_tsep_1(A_87, B_88, C_89))=k2_xboole_0(u1_struct_0(B_88), u1_struct_0(C_89)) | ~v1_pre_topc(k1_tsep_1(A_87, B_88, C_89)) | v2_struct_0(k1_tsep_1(A_87, B_88, C_89)) | ~m1_pre_topc(C_89, A_87) | v2_struct_0(C_89) | ~m1_pre_topc(B_88, A_87) | v2_struct_0(B_88) | ~l1_pre_topc(A_87) | v2_struct_0(A_87))), inference(resolution, [status(thm)], [c_12, c_145])).
% 3.94/1.71  tff(c_16, plain, (![A_21, B_22, C_23]: (~v2_struct_0(k1_tsep_1(A_21, B_22, C_23)) | ~m1_pre_topc(C_23, A_21) | v2_struct_0(C_23) | ~m1_pre_topc(B_22, A_21) | v2_struct_0(B_22) | ~l1_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.94/1.71  tff(c_223, plain, (![A_90, B_91, C_92]: (u1_struct_0(k1_tsep_1(A_90, B_91, C_92))=k2_xboole_0(u1_struct_0(B_91), u1_struct_0(C_92)) | ~v1_pre_topc(k1_tsep_1(A_90, B_91, C_92)) | ~m1_pre_topc(C_92, A_90) | v2_struct_0(C_92) | ~m1_pre_topc(B_91, A_90) | v2_struct_0(B_91) | ~l1_pre_topc(A_90) | v2_struct_0(A_90))), inference(resolution, [status(thm)], [c_153, c_16])).
% 3.94/1.71  tff(c_235, plain, (![A_96, B_97, C_98]: (u1_struct_0(k1_tsep_1(A_96, B_97, C_98))=k2_xboole_0(u1_struct_0(B_97), u1_struct_0(C_98)) | ~m1_pre_topc(C_98, A_96) | v2_struct_0(C_98) | ~m1_pre_topc(B_97, A_96) | v2_struct_0(B_97) | ~l1_pre_topc(A_96) | v2_struct_0(A_96))), inference(resolution, [status(thm)], [c_14, c_223])).
% 3.94/1.71  tff(c_84, plain, (![B_51, A_52]: (m1_subset_1(u1_struct_0(B_51), k1_zfmisc_1(u1_struct_0(A_52))) | ~m1_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.94/1.71  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.94/1.71  tff(c_88, plain, (![B_51, A_52]: (r1_tarski(u1_struct_0(B_51), u1_struct_0(A_52)) | ~m1_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_84, c_2])).
% 3.94/1.71  tff(c_301, plain, (![B_99, C_100, A_101, A_102]: (r1_tarski(k2_xboole_0(u1_struct_0(B_99), u1_struct_0(C_100)), u1_struct_0(A_101)) | ~m1_pre_topc(k1_tsep_1(A_102, B_99, C_100), A_101) | ~l1_pre_topc(A_101) | ~m1_pre_topc(C_100, A_102) | v2_struct_0(C_100) | ~m1_pre_topc(B_99, A_102) | v2_struct_0(B_99) | ~l1_pre_topc(A_102) | v2_struct_0(A_102))), inference(superposition, [status(thm), theory('equality')], [c_235, c_88])).
% 3.94/1.71  tff(c_304, plain, (![B_22, C_23, A_21]: (r1_tarski(k2_xboole_0(u1_struct_0(B_22), u1_struct_0(C_23)), u1_struct_0(A_21)) | ~m1_pre_topc(C_23, A_21) | v2_struct_0(C_23) | ~m1_pre_topc(B_22, A_21) | v2_struct_0(B_22) | ~l1_pre_topc(A_21) | v2_struct_0(A_21))), inference(resolution, [status(thm)], [c_12, c_301])).
% 3.94/1.71  tff(c_22, plain, (![B_31, C_33, A_27]: (m1_pre_topc(B_31, C_33) | ~r1_tarski(u1_struct_0(B_31), u1_struct_0(C_33)) | ~m1_pre_topc(C_33, A_27) | ~m1_pre_topc(B_31, A_27) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.94/1.71  tff(c_692, plain, (![A_163, C_162, C_159, A_161, B_160]: (m1_pre_topc(k1_tsep_1(A_161, B_160, C_159), C_162) | ~r1_tarski(k2_xboole_0(u1_struct_0(B_160), u1_struct_0(C_159)), u1_struct_0(C_162)) | ~m1_pre_topc(C_162, A_163) | ~m1_pre_topc(k1_tsep_1(A_161, B_160, C_159), A_163) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | ~m1_pre_topc(C_159, A_161) | v2_struct_0(C_159) | ~m1_pre_topc(B_160, A_161) | v2_struct_0(B_160) | ~l1_pre_topc(A_161) | v2_struct_0(A_161))), inference(superposition, [status(thm), theory('equality')], [c_235, c_22])).
% 3.94/1.71  tff(c_746, plain, (![C_170, A_171, A_169, A_172, B_173]: (m1_pre_topc(k1_tsep_1(A_171, B_173, C_170), A_169) | ~m1_pre_topc(A_169, A_172) | ~m1_pre_topc(k1_tsep_1(A_171, B_173, C_170), A_172) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | ~m1_pre_topc(C_170, A_171) | ~m1_pre_topc(B_173, A_171) | ~l1_pre_topc(A_171) | v2_struct_0(A_171) | ~m1_pre_topc(C_170, A_169) | v2_struct_0(C_170) | ~m1_pre_topc(B_173, A_169) | v2_struct_0(B_173) | ~l1_pre_topc(A_169) | v2_struct_0(A_169))), inference(resolution, [status(thm)], [c_304, c_692])).
% 3.94/1.71  tff(c_758, plain, (![A_171, B_173, C_170]: (m1_pre_topc(k1_tsep_1(A_171, B_173, C_170), '#skF_3') | ~m1_pre_topc(k1_tsep_1(A_171, B_173, C_170), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc(C_170, A_171) | ~m1_pre_topc(B_173, A_171) | ~l1_pre_topc(A_171) | v2_struct_0(A_171) | ~m1_pre_topc(C_170, '#skF_3') | v2_struct_0(C_170) | ~m1_pre_topc(B_173, '#skF_3') | v2_struct_0(B_173) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_746])).
% 3.94/1.71  tff(c_778, plain, (![A_171, B_173, C_170]: (m1_pre_topc(k1_tsep_1(A_171, B_173, C_170), '#skF_3') | ~m1_pre_topc(k1_tsep_1(A_171, B_173, C_170), '#skF_1') | ~m1_pre_topc(C_170, A_171) | ~m1_pre_topc(B_173, A_171) | ~l1_pre_topc(A_171) | v2_struct_0(A_171) | ~m1_pre_topc(C_170, '#skF_3') | v2_struct_0(C_170) | ~m1_pre_topc(B_173, '#skF_3') | v2_struct_0(B_173) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_44, c_42, c_758])).
% 3.94/1.71  tff(c_870, plain, (![A_185, B_186, C_187]: (m1_pre_topc(k1_tsep_1(A_185, B_186, C_187), '#skF_3') | ~m1_pre_topc(k1_tsep_1(A_185, B_186, C_187), '#skF_1') | ~m1_pre_topc(C_187, A_185) | ~m1_pre_topc(B_186, A_185) | ~l1_pre_topc(A_185) | v2_struct_0(A_185) | ~m1_pre_topc(C_187, '#skF_3') | v2_struct_0(C_187) | ~m1_pre_topc(B_186, '#skF_3') | v2_struct_0(B_186))), inference(negUnitSimplification, [status(thm)], [c_36, c_778])).
% 3.94/1.71  tff(c_24, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.94/1.71  tff(c_886, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_870, c_24])).
% 3.94/1.71  tff(c_905, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_42, c_38, c_30, c_886])).
% 3.94/1.71  tff(c_906, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_32, c_46, c_905])).
% 3.94/1.71  tff(c_909, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_906])).
% 3.94/1.71  tff(c_912, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_30, c_909])).
% 3.94/1.71  tff(c_914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_32, c_912])).
% 3.94/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.71  
% 3.94/1.71  Inference rules
% 3.94/1.71  ----------------------
% 3.94/1.71  #Ref     : 0
% 3.94/1.71  #Sup     : 251
% 3.94/1.71  #Fact    : 0
% 3.94/1.71  #Define  : 0
% 3.94/1.71  #Split   : 1
% 3.94/1.71  #Chain   : 0
% 3.94/1.71  #Close   : 0
% 3.94/1.71  
% 3.94/1.71  Ordering : KBO
% 3.94/1.71  
% 3.94/1.71  Simplification rules
% 3.94/1.71  ----------------------
% 3.94/1.71  #Subsume      : 45
% 3.94/1.71  #Demod        : 53
% 3.94/1.71  #Tautology    : 12
% 3.94/1.71  #SimpNegUnit  : 14
% 3.94/1.71  #BackRed      : 0
% 3.94/1.71  
% 3.94/1.71  #Partial instantiations: 0
% 3.94/1.71  #Strategies tried      : 1
% 3.94/1.71  
% 3.94/1.71  Timing (in seconds)
% 3.94/1.71  ----------------------
% 3.94/1.71  Preprocessing        : 0.31
% 3.94/1.71  Parsing              : 0.17
% 3.94/1.71  CNF conversion       : 0.03
% 3.94/1.71  Main loop            : 0.58
% 3.94/1.71  Inferencing          : 0.21
% 3.94/1.71  Reduction            : 0.15
% 3.94/1.71  Demodulation         : 0.09
% 3.94/1.71  BG Simplification    : 0.03
% 3.94/1.71  Subsumption          : 0.16
% 3.94/1.71  Abstraction          : 0.03
% 3.94/1.71  MUC search           : 0.00
% 3.94/1.71  Cooper               : 0.00
% 3.94/1.71  Total                : 0.92
% 3.94/1.71  Index Insertion      : 0.00
% 3.94/1.71  Index Deletion       : 0.00
% 3.94/1.71  Index Matching       : 0.00
% 3.94/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
