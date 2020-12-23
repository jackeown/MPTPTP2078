%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:43 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 156 expanded)
%              Number of leaves         :   29 (  71 expanded)
%              Depth                    :   21
%              Number of atoms          :  302 ( 888 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > k1_tsep_1 > k3_xboole_0 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

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

tff(f_186,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tmap_1)).

tff(f_102,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

tff(f_80,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => m1_pre_topc(B,k1_tsep_1(A,B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

tff(f_138,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_152,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_28,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_42,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_32,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_30,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_12,plain,(
    ! [A_25,B_26,C_27] :
      ( m1_pre_topc(k2_tsep_1(A_25,B_26,C_27),A_25)
      | ~ m1_pre_topc(C_27,A_25)
      | v2_struct_0(C_27)
      | ~ m1_pre_topc(B_26,A_25)
      | v2_struct_0(B_26)
      | ~ l1_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_14,plain,(
    ! [A_25,B_26,C_27] :
      ( v1_pre_topc(k2_tsep_1(A_25,B_26,C_27))
      | ~ m1_pre_topc(C_27,A_25)
      | v2_struct_0(C_27)
      | ~ m1_pre_topc(B_26,A_25)
      | v2_struct_0(B_26)
      | ~ l1_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_492,plain,(
    ! [A_103,B_104,C_105] :
      ( u1_struct_0(k2_tsep_1(A_103,B_104,C_105)) = k3_xboole_0(u1_struct_0(B_104),u1_struct_0(C_105))
      | ~ m1_pre_topc(k2_tsep_1(A_103,B_104,C_105),A_103)
      | ~ v1_pre_topc(k2_tsep_1(A_103,B_104,C_105))
      | v2_struct_0(k2_tsep_1(A_103,B_104,C_105))
      | r1_tsep_1(B_104,C_105)
      | ~ m1_pre_topc(C_105,A_103)
      | v2_struct_0(C_105)
      | ~ m1_pre_topc(B_104,A_103)
      | v2_struct_0(B_104)
      | ~ l1_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_562,plain,(
    ! [A_111,B_112,C_113] :
      ( u1_struct_0(k2_tsep_1(A_111,B_112,C_113)) = k3_xboole_0(u1_struct_0(B_112),u1_struct_0(C_113))
      | ~ v1_pre_topc(k2_tsep_1(A_111,B_112,C_113))
      | v2_struct_0(k2_tsep_1(A_111,B_112,C_113))
      | r1_tsep_1(B_112,C_113)
      | ~ m1_pre_topc(C_113,A_111)
      | v2_struct_0(C_113)
      | ~ m1_pre_topc(B_112,A_111)
      | v2_struct_0(B_112)
      | ~ l1_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_12,c_492])).

tff(c_16,plain,(
    ! [A_25,B_26,C_27] :
      ( ~ v2_struct_0(k2_tsep_1(A_25,B_26,C_27))
      | ~ m1_pre_topc(C_27,A_25)
      | v2_struct_0(C_27)
      | ~ m1_pre_topc(B_26,A_25)
      | v2_struct_0(B_26)
      | ~ l1_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_623,plain,(
    ! [A_114,B_115,C_116] :
      ( u1_struct_0(k2_tsep_1(A_114,B_115,C_116)) = k3_xboole_0(u1_struct_0(B_115),u1_struct_0(C_116))
      | ~ v1_pre_topc(k2_tsep_1(A_114,B_115,C_116))
      | r1_tsep_1(B_115,C_116)
      | ~ m1_pre_topc(C_116,A_114)
      | v2_struct_0(C_116)
      | ~ m1_pre_topc(B_115,A_114)
      | v2_struct_0(B_115)
      | ~ l1_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_562,c_16])).

tff(c_626,plain,(
    ! [A_25,B_26,C_27] :
      ( u1_struct_0(k2_tsep_1(A_25,B_26,C_27)) = k3_xboole_0(u1_struct_0(B_26),u1_struct_0(C_27))
      | r1_tsep_1(B_26,C_27)
      | ~ m1_pre_topc(C_27,A_25)
      | v2_struct_0(C_27)
      | ~ m1_pre_topc(B_26,A_25)
      | v2_struct_0(B_26)
      | ~ l1_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_14,c_623])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_51,plain,(
    ! [B_56,A_57] :
      ( l1_pre_topc(B_56)
      | ~ m1_pre_topc(B_56,A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_63,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_51])).

tff(c_74,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_63])).

tff(c_627,plain,(
    ! [A_117,B_118,C_119] :
      ( u1_struct_0(k2_tsep_1(A_117,B_118,C_119)) = k3_xboole_0(u1_struct_0(B_118),u1_struct_0(C_119))
      | r1_tsep_1(B_118,C_119)
      | ~ m1_pre_topc(C_119,A_117)
      | v2_struct_0(C_119)
      | ~ m1_pre_topc(B_118,A_117)
      | v2_struct_0(B_118)
      | ~ l1_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_14,c_623])).

tff(c_78,plain,(
    ! [B_58,A_59] :
      ( v2_pre_topc(B_58)
      | ~ m1_pre_topc(B_58,A_59)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_90,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_78])).

tff(c_101,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_90])).

tff(c_291,plain,(
    ! [B_93,A_94,C_95] :
      ( m1_pre_topc(B_93,k1_tsep_1(A_94,B_93,C_95))
      | ~ m1_pre_topc(C_95,A_94)
      | v2_struct_0(C_95)
      | ~ m1_pre_topc(B_93,A_94)
      | v2_struct_0(B_93)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_162,plain,(
    ! [A_79,B_80] :
      ( k1_tsep_1(A_79,B_80,B_80) = g1_pre_topc(u1_struct_0(B_80),u1_pre_topc(B_80))
      | ~ m1_pre_topc(B_80,A_79)
      | v2_struct_0(B_80)
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_170,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k1_tsep_1('#skF_1','#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_162])).

tff(c_187,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k1_tsep_1('#skF_1','#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_170])).

tff(c_188,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k1_tsep_1('#skF_1','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_36,c_187])).

tff(c_6,plain,(
    ! [B_9,A_7] :
      ( m1_pre_topc(B_9,A_7)
      | ~ m1_pre_topc(B_9,g1_pre_topc(u1_struct_0(A_7),u1_pre_topc(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_205,plain,(
    ! [B_9] :
      ( m1_pre_topc(B_9,'#skF_4')
      | ~ m1_pre_topc(B_9,k1_tsep_1('#skF_1','#skF_4','#skF_4'))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_6])).

tff(c_209,plain,(
    ! [B_9] :
      ( m1_pre_topc(B_9,'#skF_4')
      | ~ m1_pre_topc(B_9,k1_tsep_1('#skF_1','#skF_4','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_205])).

tff(c_295,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_291,c_209])).

tff(c_322,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_34,c_295])).

tff(c_323,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_36,c_322])).

tff(c_22,plain,(
    ! [B_42,C_44,A_38] :
      ( r1_tarski(u1_struct_0(B_42),u1_struct_0(C_44))
      | ~ m1_pre_topc(B_42,C_44)
      | ~ m1_pre_topc(C_44,A_38)
      | ~ m1_pre_topc(B_42,A_38)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_345,plain,(
    ! [B_42] :
      ( r1_tarski(u1_struct_0(B_42),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_42,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_323,c_22])).

tff(c_358,plain,(
    ! [B_42] :
      ( r1_tarski(u1_struct_0(B_42),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_42,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_74,c_345])).

tff(c_753,plain,(
    ! [B_129,C_130,A_131] :
      ( r1_tarski(k3_xboole_0(u1_struct_0(B_129),u1_struct_0(C_130)),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(k2_tsep_1(A_131,B_129,C_130),'#skF_4')
      | r1_tsep_1(B_129,C_130)
      | ~ m1_pre_topc(C_130,A_131)
      | v2_struct_0(C_130)
      | ~ m1_pre_topc(B_129,A_131)
      | v2_struct_0(B_129)
      | ~ l1_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_358])).

tff(c_756,plain,(
    ! [B_26,C_27] :
      ( r1_tarski(k3_xboole_0(u1_struct_0(B_26),u1_struct_0(C_27)),u1_struct_0('#skF_4'))
      | r1_tsep_1(B_26,C_27)
      | ~ m1_pre_topc(C_27,'#skF_4')
      | v2_struct_0(C_27)
      | ~ m1_pre_topc(B_26,'#skF_4')
      | v2_struct_0(B_26)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_753])).

tff(c_759,plain,(
    ! [B_26,C_27] :
      ( r1_tarski(k3_xboole_0(u1_struct_0(B_26),u1_struct_0(C_27)),u1_struct_0('#skF_4'))
      | r1_tsep_1(B_26,C_27)
      | ~ m1_pre_topc(C_27,'#skF_4')
      | v2_struct_0(C_27)
      | ~ m1_pre_topc(B_26,'#skF_4')
      | v2_struct_0(B_26)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_756])).

tff(c_761,plain,(
    ! [B_132,C_133] :
      ( r1_tarski(k3_xboole_0(u1_struct_0(B_132),u1_struct_0(C_133)),u1_struct_0('#skF_4'))
      | r1_tsep_1(B_132,C_133)
      | ~ m1_pre_topc(C_133,'#skF_4')
      | v2_struct_0(C_133)
      | ~ m1_pre_topc(B_132,'#skF_4')
      | v2_struct_0(B_132) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_759])).

tff(c_796,plain,(
    ! [A_142,B_143,C_144] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_142,B_143,C_144)),u1_struct_0('#skF_4'))
      | r1_tsep_1(B_143,C_144)
      | ~ m1_pre_topc(C_144,'#skF_4')
      | v2_struct_0(C_144)
      | ~ m1_pre_topc(B_143,'#skF_4')
      | v2_struct_0(B_143)
      | r1_tsep_1(B_143,C_144)
      | ~ m1_pre_topc(C_144,A_142)
      | v2_struct_0(C_144)
      | ~ m1_pre_topc(B_143,A_142)
      | v2_struct_0(B_143)
      | ~ l1_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_761])).

tff(c_24,plain,(
    ! [B_42,C_44,A_38] :
      ( m1_pre_topc(B_42,C_44)
      | ~ r1_tarski(u1_struct_0(B_42),u1_struct_0(C_44))
      | ~ m1_pre_topc(C_44,A_38)
      | ~ m1_pre_topc(B_42,A_38)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1167,plain,(
    ! [A_185,B_186,C_187,A_188] :
      ( m1_pre_topc(k2_tsep_1(A_185,B_186,C_187),'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_188)
      | ~ m1_pre_topc(k2_tsep_1(A_185,B_186,C_187),A_188)
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | ~ m1_pre_topc(C_187,'#skF_4')
      | ~ m1_pre_topc(B_186,'#skF_4')
      | r1_tsep_1(B_186,C_187)
      | ~ m1_pre_topc(C_187,A_185)
      | v2_struct_0(C_187)
      | ~ m1_pre_topc(B_186,A_185)
      | v2_struct_0(B_186)
      | ~ l1_pre_topc(A_185)
      | v2_struct_0(A_185) ) ),
    inference(resolution,[status(thm)],[c_796,c_24])).

tff(c_1188,plain,(
    ! [A_189,B_190,C_191] :
      ( m1_pre_topc(k2_tsep_1(A_189,B_190,C_191),'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_189)
      | ~ v2_pre_topc(A_189)
      | ~ m1_pre_topc(C_191,'#skF_4')
      | ~ m1_pre_topc(B_190,'#skF_4')
      | r1_tsep_1(B_190,C_191)
      | ~ m1_pre_topc(C_191,A_189)
      | v2_struct_0(C_191)
      | ~ m1_pre_topc(B_190,A_189)
      | v2_struct_0(B_190)
      | ~ l1_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_12,c_1167])).

tff(c_26,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1209,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_4')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1188,c_26])).

tff(c_1235,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_38,c_32,c_30,c_48,c_34,c_1209])).

tff(c_1237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_44,c_40,c_28,c_1235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n019.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 14:27:52 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.02/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.65  
% 4.02/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.65  %$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > k1_tsep_1 > k3_xboole_0 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.02/1.65  
% 4.02/1.65  %Foreground sorts:
% 4.02/1.65  
% 4.02/1.65  
% 4.02/1.65  %Background operators:
% 4.02/1.65  
% 4.02/1.65  
% 4.02/1.65  %Foreground operators:
% 4.02/1.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.02/1.65  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 4.02/1.65  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.02/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.02/1.65  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.02/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.02/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.02/1.65  tff('#skF_2', type, '#skF_2': $i).
% 4.02/1.65  tff('#skF_3', type, '#skF_3': $i).
% 4.02/1.65  tff('#skF_1', type, '#skF_1': $i).
% 4.02/1.65  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.02/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.02/1.65  tff('#skF_4', type, '#skF_4': $i).
% 4.02/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.02/1.65  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.02/1.65  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 4.02/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.02/1.65  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 4.02/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.02/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.02/1.65  
% 4.02/1.67  tff(f_186, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, D) & m1_pre_topc(C, D)) => (r1_tsep_1(B, C) | m1_pre_topc(k2_tsep_1(A, B, C), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tmap_1)).
% 4.02/1.67  tff(f_102, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 4.02/1.67  tff(f_80, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k2_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k3_xboole_0(u1_struct_0(B), u1_struct_0(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tsep_1)).
% 4.02/1.67  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.02/1.67  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.02/1.67  tff(f_123, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => m1_pre_topc(B, k1_tsep_1(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tsep_1)).
% 4.02/1.67  tff(f_138, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 4.02/1.67  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 4.02/1.67  tff(f_152, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 4.02/1.67  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.02/1.67  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.02/1.67  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.02/1.67  tff(c_28, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.02/1.67  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.02/1.67  tff(c_42, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.02/1.67  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.02/1.67  tff(c_32, plain, (m1_pre_topc('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.02/1.67  tff(c_30, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.02/1.67  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.02/1.67  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.02/1.67  tff(c_12, plain, (![A_25, B_26, C_27]: (m1_pre_topc(k2_tsep_1(A_25, B_26, C_27), A_25) | ~m1_pre_topc(C_27, A_25) | v2_struct_0(C_27) | ~m1_pre_topc(B_26, A_25) | v2_struct_0(B_26) | ~l1_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.02/1.67  tff(c_14, plain, (![A_25, B_26, C_27]: (v1_pre_topc(k2_tsep_1(A_25, B_26, C_27)) | ~m1_pre_topc(C_27, A_25) | v2_struct_0(C_27) | ~m1_pre_topc(B_26, A_25) | v2_struct_0(B_26) | ~l1_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.02/1.67  tff(c_492, plain, (![A_103, B_104, C_105]: (u1_struct_0(k2_tsep_1(A_103, B_104, C_105))=k3_xboole_0(u1_struct_0(B_104), u1_struct_0(C_105)) | ~m1_pre_topc(k2_tsep_1(A_103, B_104, C_105), A_103) | ~v1_pre_topc(k2_tsep_1(A_103, B_104, C_105)) | v2_struct_0(k2_tsep_1(A_103, B_104, C_105)) | r1_tsep_1(B_104, C_105) | ~m1_pre_topc(C_105, A_103) | v2_struct_0(C_105) | ~m1_pre_topc(B_104, A_103) | v2_struct_0(B_104) | ~l1_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.02/1.67  tff(c_562, plain, (![A_111, B_112, C_113]: (u1_struct_0(k2_tsep_1(A_111, B_112, C_113))=k3_xboole_0(u1_struct_0(B_112), u1_struct_0(C_113)) | ~v1_pre_topc(k2_tsep_1(A_111, B_112, C_113)) | v2_struct_0(k2_tsep_1(A_111, B_112, C_113)) | r1_tsep_1(B_112, C_113) | ~m1_pre_topc(C_113, A_111) | v2_struct_0(C_113) | ~m1_pre_topc(B_112, A_111) | v2_struct_0(B_112) | ~l1_pre_topc(A_111) | v2_struct_0(A_111))), inference(resolution, [status(thm)], [c_12, c_492])).
% 4.02/1.67  tff(c_16, plain, (![A_25, B_26, C_27]: (~v2_struct_0(k2_tsep_1(A_25, B_26, C_27)) | ~m1_pre_topc(C_27, A_25) | v2_struct_0(C_27) | ~m1_pre_topc(B_26, A_25) | v2_struct_0(B_26) | ~l1_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.02/1.67  tff(c_623, plain, (![A_114, B_115, C_116]: (u1_struct_0(k2_tsep_1(A_114, B_115, C_116))=k3_xboole_0(u1_struct_0(B_115), u1_struct_0(C_116)) | ~v1_pre_topc(k2_tsep_1(A_114, B_115, C_116)) | r1_tsep_1(B_115, C_116) | ~m1_pre_topc(C_116, A_114) | v2_struct_0(C_116) | ~m1_pre_topc(B_115, A_114) | v2_struct_0(B_115) | ~l1_pre_topc(A_114) | v2_struct_0(A_114))), inference(resolution, [status(thm)], [c_562, c_16])).
% 4.02/1.67  tff(c_626, plain, (![A_25, B_26, C_27]: (u1_struct_0(k2_tsep_1(A_25, B_26, C_27))=k3_xboole_0(u1_struct_0(B_26), u1_struct_0(C_27)) | r1_tsep_1(B_26, C_27) | ~m1_pre_topc(C_27, A_25) | v2_struct_0(C_27) | ~m1_pre_topc(B_26, A_25) | v2_struct_0(B_26) | ~l1_pre_topc(A_25) | v2_struct_0(A_25))), inference(resolution, [status(thm)], [c_14, c_623])).
% 4.02/1.67  tff(c_36, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.02/1.67  tff(c_51, plain, (![B_56, A_57]: (l1_pre_topc(B_56) | ~m1_pre_topc(B_56, A_57) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.02/1.67  tff(c_63, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_51])).
% 4.02/1.67  tff(c_74, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_63])).
% 4.02/1.67  tff(c_627, plain, (![A_117, B_118, C_119]: (u1_struct_0(k2_tsep_1(A_117, B_118, C_119))=k3_xboole_0(u1_struct_0(B_118), u1_struct_0(C_119)) | r1_tsep_1(B_118, C_119) | ~m1_pre_topc(C_119, A_117) | v2_struct_0(C_119) | ~m1_pre_topc(B_118, A_117) | v2_struct_0(B_118) | ~l1_pre_topc(A_117) | v2_struct_0(A_117))), inference(resolution, [status(thm)], [c_14, c_623])).
% 4.02/1.67  tff(c_78, plain, (![B_58, A_59]: (v2_pre_topc(B_58) | ~m1_pre_topc(B_58, A_59) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.02/1.67  tff(c_90, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_78])).
% 4.02/1.67  tff(c_101, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_90])).
% 4.02/1.67  tff(c_291, plain, (![B_93, A_94, C_95]: (m1_pre_topc(B_93, k1_tsep_1(A_94, B_93, C_95)) | ~m1_pre_topc(C_95, A_94) | v2_struct_0(C_95) | ~m1_pre_topc(B_93, A_94) | v2_struct_0(B_93) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.02/1.67  tff(c_162, plain, (![A_79, B_80]: (k1_tsep_1(A_79, B_80, B_80)=g1_pre_topc(u1_struct_0(B_80), u1_pre_topc(B_80)) | ~m1_pre_topc(B_80, A_79) | v2_struct_0(B_80) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.02/1.67  tff(c_170, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k1_tsep_1('#skF_1', '#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_162])).
% 4.02/1.67  tff(c_187, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k1_tsep_1('#skF_1', '#skF_4', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_170])).
% 4.02/1.67  tff(c_188, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k1_tsep_1('#skF_1', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_36, c_187])).
% 4.02/1.67  tff(c_6, plain, (![B_9, A_7]: (m1_pre_topc(B_9, A_7) | ~m1_pre_topc(B_9, g1_pre_topc(u1_struct_0(A_7), u1_pre_topc(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.02/1.67  tff(c_205, plain, (![B_9]: (m1_pre_topc(B_9, '#skF_4') | ~m1_pre_topc(B_9, k1_tsep_1('#skF_1', '#skF_4', '#skF_4')) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_188, c_6])).
% 4.02/1.67  tff(c_209, plain, (![B_9]: (m1_pre_topc(B_9, '#skF_4') | ~m1_pre_topc(B_9, k1_tsep_1('#skF_1', '#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_205])).
% 4.02/1.67  tff(c_295, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_291, c_209])).
% 4.02/1.67  tff(c_322, plain, (m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_34, c_295])).
% 4.02/1.67  tff(c_323, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_36, c_322])).
% 4.02/1.67  tff(c_22, plain, (![B_42, C_44, A_38]: (r1_tarski(u1_struct_0(B_42), u1_struct_0(C_44)) | ~m1_pre_topc(B_42, C_44) | ~m1_pre_topc(C_44, A_38) | ~m1_pre_topc(B_42, A_38) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.02/1.67  tff(c_345, plain, (![B_42]: (r1_tarski(u1_struct_0(B_42), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_42, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_323, c_22])).
% 4.02/1.67  tff(c_358, plain, (![B_42]: (r1_tarski(u1_struct_0(B_42), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_42, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_74, c_345])).
% 4.02/1.67  tff(c_753, plain, (![B_129, C_130, A_131]: (r1_tarski(k3_xboole_0(u1_struct_0(B_129), u1_struct_0(C_130)), u1_struct_0('#skF_4')) | ~m1_pre_topc(k2_tsep_1(A_131, B_129, C_130), '#skF_4') | r1_tsep_1(B_129, C_130) | ~m1_pre_topc(C_130, A_131) | v2_struct_0(C_130) | ~m1_pre_topc(B_129, A_131) | v2_struct_0(B_129) | ~l1_pre_topc(A_131) | v2_struct_0(A_131))), inference(superposition, [status(thm), theory('equality')], [c_627, c_358])).
% 4.02/1.67  tff(c_756, plain, (![B_26, C_27]: (r1_tarski(k3_xboole_0(u1_struct_0(B_26), u1_struct_0(C_27)), u1_struct_0('#skF_4')) | r1_tsep_1(B_26, C_27) | ~m1_pre_topc(C_27, '#skF_4') | v2_struct_0(C_27) | ~m1_pre_topc(B_26, '#skF_4') | v2_struct_0(B_26) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_753])).
% 4.02/1.67  tff(c_759, plain, (![B_26, C_27]: (r1_tarski(k3_xboole_0(u1_struct_0(B_26), u1_struct_0(C_27)), u1_struct_0('#skF_4')) | r1_tsep_1(B_26, C_27) | ~m1_pre_topc(C_27, '#skF_4') | v2_struct_0(C_27) | ~m1_pre_topc(B_26, '#skF_4') | v2_struct_0(B_26) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_756])).
% 4.02/1.67  tff(c_761, plain, (![B_132, C_133]: (r1_tarski(k3_xboole_0(u1_struct_0(B_132), u1_struct_0(C_133)), u1_struct_0('#skF_4')) | r1_tsep_1(B_132, C_133) | ~m1_pre_topc(C_133, '#skF_4') | v2_struct_0(C_133) | ~m1_pre_topc(B_132, '#skF_4') | v2_struct_0(B_132))), inference(negUnitSimplification, [status(thm)], [c_36, c_759])).
% 4.02/1.67  tff(c_796, plain, (![A_142, B_143, C_144]: (r1_tarski(u1_struct_0(k2_tsep_1(A_142, B_143, C_144)), u1_struct_0('#skF_4')) | r1_tsep_1(B_143, C_144) | ~m1_pre_topc(C_144, '#skF_4') | v2_struct_0(C_144) | ~m1_pre_topc(B_143, '#skF_4') | v2_struct_0(B_143) | r1_tsep_1(B_143, C_144) | ~m1_pre_topc(C_144, A_142) | v2_struct_0(C_144) | ~m1_pre_topc(B_143, A_142) | v2_struct_0(B_143) | ~l1_pre_topc(A_142) | v2_struct_0(A_142))), inference(superposition, [status(thm), theory('equality')], [c_626, c_761])).
% 4.02/1.67  tff(c_24, plain, (![B_42, C_44, A_38]: (m1_pre_topc(B_42, C_44) | ~r1_tarski(u1_struct_0(B_42), u1_struct_0(C_44)) | ~m1_pre_topc(C_44, A_38) | ~m1_pre_topc(B_42, A_38) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.02/1.67  tff(c_1167, plain, (![A_185, B_186, C_187, A_188]: (m1_pre_topc(k2_tsep_1(A_185, B_186, C_187), '#skF_4') | ~m1_pre_topc('#skF_4', A_188) | ~m1_pre_topc(k2_tsep_1(A_185, B_186, C_187), A_188) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | ~m1_pre_topc(C_187, '#skF_4') | ~m1_pre_topc(B_186, '#skF_4') | r1_tsep_1(B_186, C_187) | ~m1_pre_topc(C_187, A_185) | v2_struct_0(C_187) | ~m1_pre_topc(B_186, A_185) | v2_struct_0(B_186) | ~l1_pre_topc(A_185) | v2_struct_0(A_185))), inference(resolution, [status(thm)], [c_796, c_24])).
% 4.02/1.67  tff(c_1188, plain, (![A_189, B_190, C_191]: (m1_pre_topc(k2_tsep_1(A_189, B_190, C_191), '#skF_4') | ~m1_pre_topc('#skF_4', A_189) | ~v2_pre_topc(A_189) | ~m1_pre_topc(C_191, '#skF_4') | ~m1_pre_topc(B_190, '#skF_4') | r1_tsep_1(B_190, C_191) | ~m1_pre_topc(C_191, A_189) | v2_struct_0(C_191) | ~m1_pre_topc(B_190, A_189) | v2_struct_0(B_190) | ~l1_pre_topc(A_189) | v2_struct_0(A_189))), inference(resolution, [status(thm)], [c_12, c_1167])).
% 4.02/1.67  tff(c_26, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.02/1.67  tff(c_1209, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_2', '#skF_4') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1188, c_26])).
% 4.02/1.67  tff(c_1235, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_38, c_32, c_30, c_48, c_34, c_1209])).
% 4.02/1.67  tff(c_1237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_44, c_40, c_28, c_1235])).
% 4.02/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.67  
% 4.02/1.67  Inference rules
% 4.02/1.67  ----------------------
% 4.02/1.67  #Ref     : 0
% 4.02/1.67  #Sup     : 272
% 4.02/1.67  #Fact    : 0
% 4.02/1.67  #Define  : 0
% 4.02/1.67  #Split   : 5
% 4.02/1.67  #Chain   : 0
% 4.02/1.67  #Close   : 0
% 4.02/1.67  
% 4.02/1.67  Ordering : KBO
% 4.02/1.67  
% 4.02/1.67  Simplification rules
% 4.02/1.67  ----------------------
% 4.02/1.67  #Subsume      : 65
% 4.02/1.67  #Demod        : 295
% 4.02/1.67  #Tautology    : 61
% 4.02/1.67  #SimpNegUnit  : 49
% 4.02/1.67  #BackRed      : 4
% 4.02/1.67  
% 4.02/1.67  #Partial instantiations: 0
% 4.02/1.67  #Strategies tried      : 1
% 4.02/1.67  
% 4.02/1.67  Timing (in seconds)
% 4.02/1.67  ----------------------
% 4.02/1.67  Preprocessing        : 0.32
% 4.02/1.67  Parsing              : 0.18
% 4.02/1.67  CNF conversion       : 0.03
% 4.02/1.67  Main loop            : 0.61
% 4.02/1.67  Inferencing          : 0.22
% 4.02/1.67  Reduction            : 0.19
% 4.02/1.67  Demodulation         : 0.13
% 4.02/1.67  BG Simplification    : 0.03
% 4.02/1.67  Subsumption          : 0.15
% 4.02/1.67  Abstraction          : 0.03
% 4.02/1.67  MUC search           : 0.00
% 4.02/1.67  Cooper               : 0.00
% 4.02/1.67  Total                : 0.96
% 4.02/1.67  Index Insertion      : 0.00
% 4.02/1.67  Index Deletion       : 0.00
% 4.02/1.67  Index Matching       : 0.00
% 4.02/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
