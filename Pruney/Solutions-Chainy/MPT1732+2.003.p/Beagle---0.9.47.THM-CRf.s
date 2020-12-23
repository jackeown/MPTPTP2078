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
% DateTime   : Thu Dec  3 10:26:47 EST 2020

% Result     : Theorem 4.21s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :  217 (1211 expanded)
%              Number of leaves         :   18 ( 444 expanded)
%              Depth                    :   15
%              Number of atoms          :  849 (9041 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(f_157,negated_conjecture,(
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
                   => ( ~ r1_tsep_1(B,C)
                     => ( ( ~ r1_tsep_1(k2_tsep_1(A,B,C),D)
                         => ( ~ r1_tsep_1(B,D)
                            & ~ r1_tsep_1(C,D) ) )
                        & ( ~ r1_tsep_1(D,k2_tsep_1(A,B,C))
                         => ( ~ r1_tsep_1(D,B)
                            & ~ r1_tsep_1(D,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tmap_1)).

tff(f_110,axiom,(
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
             => ( ~ r1_tsep_1(B,C)
               => ( m1_pre_topc(k2_tsep_1(A,B,C),B)
                  & m1_pre_topc(k2_tsep_1(A,B,C),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tsep_1)).

tff(f_47,axiom,(
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

tff(f_84,axiom,(
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
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ( m1_pre_topc(B,C)
                   => ( ( r1_tsep_1(B,D)
                        & r1_tsep_1(D,B) )
                      | ( ~ r1_tsep_1(C,D)
                        & ~ r1_tsep_1(D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_30,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_20,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_18,plain,(
    ! [A_19,B_23,C_25] :
      ( m1_pre_topc(k2_tsep_1(A_19,B_23,C_25),B_23)
      | r1_tsep_1(B_23,C_25)
      | ~ m1_pre_topc(C_25,A_19)
      | v2_struct_0(C_25)
      | ~ m1_pre_topc(B_23,A_19)
      | v2_struct_0(B_23)
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( m1_pre_topc(k2_tsep_1(A_1,B_2,C_3),A_1)
      | ~ m1_pre_topc(C_3,A_1)
      | v2_struct_0(C_3)
      | ~ m1_pre_topc(B_2,A_1)
      | v2_struct_0(B_2)
      | ~ l1_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_16,plain,(
    ! [A_19,B_23,C_25] :
      ( m1_pre_topc(k2_tsep_1(A_19,B_23,C_25),C_25)
      | r1_tsep_1(B_23,C_25)
      | ~ m1_pre_topc(C_25,A_19)
      | v2_struct_0(C_25)
      | ~ m1_pre_topc(B_23,A_19)
      | v2_struct_0(B_23)
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_40,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_49,plain,(
    r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_55,plain,(
    ! [D_52,B_53,C_54,A_55] :
      ( r1_tsep_1(D_52,B_53)
      | ~ r1_tsep_1(D_52,C_54)
      | ~ m1_pre_topc(B_53,C_54)
      | ~ m1_pre_topc(D_52,A_55)
      | v2_struct_0(D_52)
      | ~ m1_pre_topc(C_54,A_55)
      | v2_struct_0(C_54)
      | ~ m1_pre_topc(B_53,A_55)
      | v2_struct_0(B_53)
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_57,plain,(
    ! [B_53,A_55] :
      ( r1_tsep_1('#skF_4',B_53)
      | ~ m1_pre_topc(B_53,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_55)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2',A_55)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_53,A_55)
      | v2_struct_0(B_53)
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_49,c_55])).

tff(c_61,plain,(
    ! [B_56,A_57] :
      ( r1_tsep_1('#skF_4',B_56)
      | ~ m1_pre_topc(B_56,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_57)
      | ~ m1_pre_topc('#skF_2',A_57)
      | ~ m1_pre_topc(B_56,A_57)
      | v2_struct_0(B_56)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_24,c_57])).

tff(c_63,plain,(
    ! [B_56] :
      ( r1_tsep_1('#skF_4',B_56)
      | ~ m1_pre_topc(B_56,'#skF_2')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_56,'#skF_1')
      | v2_struct_0(B_56)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_61])).

tff(c_66,plain,(
    ! [B_56] :
      ( r1_tsep_1('#skF_4',B_56)
      | ~ m1_pre_topc(B_56,'#skF_2')
      | ~ m1_pre_topc(B_56,'#skF_1')
      | v2_struct_0(B_56)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_63])).

tff(c_68,plain,(
    ! [B_58] :
      ( r1_tsep_1('#skF_4',B_58)
      | ~ m1_pre_topc(B_58,'#skF_2')
      | ~ m1_pre_topc(B_58,'#skF_1')
      | v2_struct_0(B_58) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_66])).

tff(c_44,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_2','#skF_4')
    | ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_48,plain,(
    ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_77,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_48])).

tff(c_89,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_92,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_89])).

tff(c_95,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_92])).

tff(c_97,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_95])).

tff(c_98,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_125,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_128,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_125])).

tff(c_131,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_128])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_131])).

tff(c_134,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_6,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ v2_struct_0(k2_tsep_1(A_1,B_2,C_3))
      | ~ m1_pre_topc(C_3,A_1)
      | v2_struct_0(C_3)
      | ~ m1_pre_topc(B_2,A_1)
      | v2_struct_0(B_2)
      | ~ l1_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_138,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_134,c_6])).

tff(c_141,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_138])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_141])).

tff(c_144,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_146,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_158,plain,(
    ! [B_85,D_86,C_87,A_88] :
      ( r1_tsep_1(B_85,D_86)
      | ~ r1_tsep_1(C_87,D_86)
      | ~ m1_pre_topc(B_85,C_87)
      | ~ m1_pre_topc(D_86,A_88)
      | v2_struct_0(D_86)
      | ~ m1_pre_topc(C_87,A_88)
      | v2_struct_0(C_87)
      | ~ m1_pre_topc(B_85,A_88)
      | v2_struct_0(B_85)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_160,plain,(
    ! [B_85,A_88] :
      ( r1_tsep_1(B_85,'#skF_4')
      | ~ m1_pre_topc(B_85,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_88)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_88)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_85,A_88)
      | v2_struct_0(B_85)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_146,c_158])).

tff(c_182,plain,(
    ! [B_92,A_93] :
      ( r1_tsep_1(B_92,'#skF_4')
      | ~ m1_pre_topc(B_92,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_93)
      | ~ m1_pre_topc('#skF_3',A_93)
      | ~ m1_pre_topc(B_92,A_93)
      | v2_struct_0(B_92)
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_24,c_160])).

tff(c_184,plain,(
    ! [B_92] :
      ( r1_tsep_1(B_92,'#skF_4')
      | ~ m1_pre_topc(B_92,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_92,'#skF_1')
      | v2_struct_0(B_92)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_182])).

tff(c_187,plain,(
    ! [B_92] :
      ( r1_tsep_1(B_92,'#skF_4')
      | ~ m1_pre_topc(B_92,'#skF_3')
      | ~ m1_pre_topc(B_92,'#skF_1')
      | v2_struct_0(B_92)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_184])).

tff(c_189,plain,(
    ! [B_94] :
      ( r1_tsep_1(B_94,'#skF_4')
      | ~ m1_pre_topc(B_94,'#skF_3')
      | ~ m1_pre_topc(B_94,'#skF_1')
      | v2_struct_0(B_94) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_187])).

tff(c_42,plain,
    ( ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_47,plain,(
    ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_203,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_189,c_47])).

tff(c_204,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_207,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_204])).

tff(c_210,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_207])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_210])).

tff(c_213,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_215,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_218,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_215])).

tff(c_221,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_218])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_221])).

tff(c_224,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_244,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_224,c_6])).

tff(c_247,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_244])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_247])).

tff(c_250,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_252,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_320,plain,(
    ! [D_128,B_129,C_130,A_131] :
      ( r1_tsep_1(D_128,B_129)
      | ~ r1_tsep_1(D_128,C_130)
      | ~ m1_pre_topc(B_129,C_130)
      | ~ m1_pre_topc(D_128,A_131)
      | v2_struct_0(D_128)
      | ~ m1_pre_topc(C_130,A_131)
      | v2_struct_0(C_130)
      | ~ m1_pre_topc(B_129,A_131)
      | v2_struct_0(B_129)
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_326,plain,(
    ! [B_129,A_131] :
      ( r1_tsep_1('#skF_4',B_129)
      | ~ m1_pre_topc(B_129,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_131)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_131)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_129,A_131)
      | v2_struct_0(B_129)
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(resolution,[status(thm)],[c_252,c_320])).

tff(c_352,plain,(
    ! [B_136,A_137] :
      ( r1_tsep_1('#skF_4',B_136)
      | ~ m1_pre_topc(B_136,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_137)
      | ~ m1_pre_topc('#skF_3',A_137)
      | ~ m1_pre_topc(B_136,A_137)
      | v2_struct_0(B_136)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_24,c_326])).

tff(c_354,plain,(
    ! [B_136] :
      ( r1_tsep_1('#skF_4',B_136)
      | ~ m1_pre_topc(B_136,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_136,'#skF_1')
      | v2_struct_0(B_136)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_352])).

tff(c_357,plain,(
    ! [B_136] :
      ( r1_tsep_1('#skF_4',B_136)
      | ~ m1_pre_topc(B_136,'#skF_3')
      | ~ m1_pre_topc(B_136,'#skF_1')
      | v2_struct_0(B_136)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_354])).

tff(c_359,plain,(
    ! [B_138] :
      ( r1_tsep_1('#skF_4',B_138)
      | ~ m1_pre_topc(B_138,'#skF_3')
      | ~ m1_pre_topc(B_138,'#skF_1')
      | v2_struct_0(B_138) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_357])).

tff(c_390,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_359,c_48])).

tff(c_430,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_433,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_430])).

tff(c_436,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_433])).

tff(c_438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_436])).

tff(c_439,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_441,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_439])).

tff(c_444,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_441])).

tff(c_447,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_444])).

tff(c_449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_447])).

tff(c_450,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_439])).

tff(c_454,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_450,c_6])).

tff(c_457,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_454])).

tff(c_459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_457])).

tff(c_460,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_467,plain,(
    ! [B_157,D_158,C_159,A_160] :
      ( r1_tsep_1(B_157,D_158)
      | ~ r1_tsep_1(C_159,D_158)
      | ~ m1_pre_topc(B_157,C_159)
      | ~ m1_pre_topc(D_158,A_160)
      | v2_struct_0(D_158)
      | ~ m1_pre_topc(C_159,A_160)
      | v2_struct_0(C_159)
      | ~ m1_pre_topc(B_157,A_160)
      | v2_struct_0(B_157)
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_469,plain,(
    ! [B_157,A_160] :
      ( r1_tsep_1(B_157,'#skF_4')
      | ~ m1_pre_topc(B_157,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_160)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2',A_160)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_157,A_160)
      | v2_struct_0(B_157)
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(resolution,[status(thm)],[c_460,c_467])).

tff(c_473,plain,(
    ! [B_161,A_162] :
      ( r1_tsep_1(B_161,'#skF_4')
      | ~ m1_pre_topc(B_161,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_162)
      | ~ m1_pre_topc('#skF_2',A_162)
      | ~ m1_pre_topc(B_161,A_162)
      | v2_struct_0(B_161)
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_24,c_469])).

tff(c_475,plain,(
    ! [B_161] :
      ( r1_tsep_1(B_161,'#skF_4')
      | ~ m1_pre_topc(B_161,'#skF_2')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_161,'#skF_1')
      | v2_struct_0(B_161)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_473])).

tff(c_478,plain,(
    ! [B_161] :
      ( r1_tsep_1(B_161,'#skF_4')
      | ~ m1_pre_topc(B_161,'#skF_2')
      | ~ m1_pre_topc(B_161,'#skF_1')
      | v2_struct_0(B_161)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_475])).

tff(c_480,plain,(
    ! [B_163] :
      ( r1_tsep_1(B_163,'#skF_4')
      | ~ m1_pre_topc(B_163,'#skF_2')
      | ~ m1_pre_topc(B_163,'#skF_1')
      | v2_struct_0(B_163) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_478])).

tff(c_496,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_480,c_47])).

tff(c_497,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_500,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_497])).

tff(c_503,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_500])).

tff(c_505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_503])).

tff(c_506,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_508,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_506])).

tff(c_511,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_508])).

tff(c_514,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_511])).

tff(c_516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_514])).

tff(c_517,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_532,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_517,c_6])).

tff(c_535,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_532])).

tff(c_537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_535])).

tff(c_538,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_540,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_538])).

tff(c_614,plain,(
    ! [B_197,D_198,C_199,A_200] :
      ( r1_tsep_1(B_197,D_198)
      | ~ r1_tsep_1(C_199,D_198)
      | ~ m1_pre_topc(B_197,C_199)
      | ~ m1_pre_topc(D_198,A_200)
      | v2_struct_0(D_198)
      | ~ m1_pre_topc(C_199,A_200)
      | v2_struct_0(C_199)
      | ~ m1_pre_topc(B_197,A_200)
      | v2_struct_0(B_197)
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200)
      | v2_struct_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_622,plain,(
    ! [B_197,A_200] :
      ( r1_tsep_1(B_197,'#skF_4')
      | ~ m1_pre_topc(B_197,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_200)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_200)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_197,A_200)
      | v2_struct_0(B_197)
      | ~ l1_pre_topc(A_200)
      | ~ v2_pre_topc(A_200)
      | v2_struct_0(A_200) ) ),
    inference(resolution,[status(thm)],[c_540,c_614])).

tff(c_656,plain,(
    ! [B_205,A_206] :
      ( r1_tsep_1(B_205,'#skF_4')
      | ~ m1_pre_topc(B_205,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_206)
      | ~ m1_pre_topc('#skF_3',A_206)
      | ~ m1_pre_topc(B_205,A_206)
      | v2_struct_0(B_205)
      | ~ l1_pre_topc(A_206)
      | ~ v2_pre_topc(A_206)
      | v2_struct_0(A_206) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_24,c_622])).

tff(c_658,plain,(
    ! [B_205] :
      ( r1_tsep_1(B_205,'#skF_4')
      | ~ m1_pre_topc(B_205,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_205,'#skF_1')
      | v2_struct_0(B_205)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_656])).

tff(c_661,plain,(
    ! [B_205] :
      ( r1_tsep_1(B_205,'#skF_4')
      | ~ m1_pre_topc(B_205,'#skF_3')
      | ~ m1_pre_topc(B_205,'#skF_1')
      | v2_struct_0(B_205)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_658])).

tff(c_663,plain,(
    ! [B_207] :
      ( r1_tsep_1(B_207,'#skF_4')
      | ~ m1_pre_topc(B_207,'#skF_3')
      | ~ m1_pre_topc(B_207,'#skF_1')
      | v2_struct_0(B_207) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_661])).

tff(c_687,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_663,c_47])).

tff(c_688,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_687])).

tff(c_698,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_688])).

tff(c_701,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_698])).

tff(c_703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_701])).

tff(c_704,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_687])).

tff(c_706,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_704])).

tff(c_709,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_706])).

tff(c_712,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_709])).

tff(c_714,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_712])).

tff(c_715,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_704])).

tff(c_719,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_715,c_6])).

tff(c_722,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_719])).

tff(c_724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_722])).

tff(c_725,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_538])).

tff(c_892,plain,(
    ! [B_252,D_253,C_254,A_255] :
      ( r1_tsep_1(B_252,D_253)
      | ~ r1_tsep_1(C_254,D_253)
      | ~ m1_pre_topc(B_252,C_254)
      | ~ m1_pre_topc(D_253,A_255)
      | v2_struct_0(D_253)
      | ~ m1_pre_topc(C_254,A_255)
      | v2_struct_0(C_254)
      | ~ m1_pre_topc(B_252,A_255)
      | v2_struct_0(B_252)
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_902,plain,(
    ! [B_252,A_255] :
      ( r1_tsep_1(B_252,'#skF_4')
      | ~ m1_pre_topc(B_252,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_255)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2',A_255)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_252,A_255)
      | v2_struct_0(B_252)
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255) ) ),
    inference(resolution,[status(thm)],[c_725,c_892])).

tff(c_918,plain,(
    ! [B_256,A_257] :
      ( r1_tsep_1(B_256,'#skF_4')
      | ~ m1_pre_topc(B_256,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_257)
      | ~ m1_pre_topc('#skF_2',A_257)
      | ~ m1_pre_topc(B_256,A_257)
      | v2_struct_0(B_256)
      | ~ l1_pre_topc(A_257)
      | ~ v2_pre_topc(A_257)
      | v2_struct_0(A_257) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_24,c_902])).

tff(c_920,plain,(
    ! [B_256] :
      ( r1_tsep_1(B_256,'#skF_4')
      | ~ m1_pre_topc(B_256,'#skF_2')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_256,'#skF_1')
      | v2_struct_0(B_256)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_918])).

tff(c_923,plain,(
    ! [B_256] :
      ( r1_tsep_1(B_256,'#skF_4')
      | ~ m1_pre_topc(B_256,'#skF_2')
      | ~ m1_pre_topc(B_256,'#skF_1')
      | v2_struct_0(B_256)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_920])).

tff(c_925,plain,(
    ! [B_258] :
      ( r1_tsep_1(B_258,'#skF_4')
      | ~ m1_pre_topc(B_258,'#skF_2')
      | ~ m1_pre_topc(B_258,'#skF_1')
      | v2_struct_0(B_258) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_923])).

tff(c_955,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_925,c_47])).

tff(c_956,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_955])).

tff(c_970,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_956])).

tff(c_973,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_970])).

tff(c_975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_973])).

tff(c_976,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_955])).

tff(c_1013,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_976])).

tff(c_1016,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1013])).

tff(c_1019,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_1016])).

tff(c_1021,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_1019])).

tff(c_1022,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_976])).

tff(c_1026,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1022,c_6])).

tff(c_1029,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_1026])).

tff(c_1031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_1029])).

tff(c_1032,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1034,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1032])).

tff(c_1075,plain,(
    ! [D_284,B_285,C_286,A_287] :
      ( r1_tsep_1(D_284,B_285)
      | ~ r1_tsep_1(D_284,C_286)
      | ~ m1_pre_topc(B_285,C_286)
      | ~ m1_pre_topc(D_284,A_287)
      | v2_struct_0(D_284)
      | ~ m1_pre_topc(C_286,A_287)
      | v2_struct_0(C_286)
      | ~ m1_pre_topc(B_285,A_287)
      | v2_struct_0(B_285)
      | ~ l1_pre_topc(A_287)
      | ~ v2_pre_topc(A_287)
      | v2_struct_0(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1081,plain,(
    ! [B_285,A_287] :
      ( r1_tsep_1('#skF_4',B_285)
      | ~ m1_pre_topc(B_285,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_287)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_287)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_285,A_287)
      | v2_struct_0(B_285)
      | ~ l1_pre_topc(A_287)
      | ~ v2_pre_topc(A_287)
      | v2_struct_0(A_287) ) ),
    inference(resolution,[status(thm)],[c_1034,c_1075])).

tff(c_1091,plain,(
    ! [B_288,A_289] :
      ( r1_tsep_1('#skF_4',B_288)
      | ~ m1_pre_topc(B_288,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_289)
      | ~ m1_pre_topc('#skF_3',A_289)
      | ~ m1_pre_topc(B_288,A_289)
      | v2_struct_0(B_288)
      | ~ l1_pre_topc(A_289)
      | ~ v2_pre_topc(A_289)
      | v2_struct_0(A_289) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_24,c_1081])).

tff(c_1093,plain,(
    ! [B_288] :
      ( r1_tsep_1('#skF_4',B_288)
      | ~ m1_pre_topc(B_288,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_288,'#skF_1')
      | v2_struct_0(B_288)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_1091])).

tff(c_1096,plain,(
    ! [B_288] :
      ( r1_tsep_1('#skF_4',B_288)
      | ~ m1_pre_topc(B_288,'#skF_3')
      | ~ m1_pre_topc(B_288,'#skF_1')
      | v2_struct_0(B_288)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_1093])).

tff(c_1098,plain,(
    ! [B_290] :
      ( r1_tsep_1('#skF_4',B_290)
      | ~ m1_pre_topc(B_290,'#skF_3')
      | ~ m1_pre_topc(B_290,'#skF_1')
      | v2_struct_0(B_290) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1096])).

tff(c_1035,plain,(
    ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_1112,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1098,c_1035])).

tff(c_1113,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1112])).

tff(c_1116,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_1113])).

tff(c_1119,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_1116])).

tff(c_1121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_1119])).

tff(c_1122,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1112])).

tff(c_1145,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1122])).

tff(c_1148,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_1145])).

tff(c_1151,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_1148])).

tff(c_1153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_1151])).

tff(c_1154,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1122])).

tff(c_1165,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1154,c_6])).

tff(c_1168,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_1165])).

tff(c_1170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_1168])).

tff(c_1172,plain,(
    r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1033,plain,(
    r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_46,plain,
    ( ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1172,c_1033,c_46])).

tff(c_1176,plain,(
    r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1032])).

tff(c_1253,plain,(
    ! [D_326,B_327,C_328,A_329] :
      ( r1_tsep_1(D_326,B_327)
      | ~ r1_tsep_1(D_326,C_328)
      | ~ m1_pre_topc(B_327,C_328)
      | ~ m1_pre_topc(D_326,A_329)
      | v2_struct_0(D_326)
      | ~ m1_pre_topc(C_328,A_329)
      | v2_struct_0(C_328)
      | ~ m1_pre_topc(B_327,A_329)
      | v2_struct_0(B_327)
      | ~ l1_pre_topc(A_329)
      | ~ v2_pre_topc(A_329)
      | v2_struct_0(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1261,plain,(
    ! [B_327,A_329] :
      ( r1_tsep_1('#skF_4',B_327)
      | ~ m1_pre_topc(B_327,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_329)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2',A_329)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_327,A_329)
      | v2_struct_0(B_327)
      | ~ l1_pre_topc(A_329)
      | ~ v2_pre_topc(A_329)
      | v2_struct_0(A_329) ) ),
    inference(resolution,[status(thm)],[c_1176,c_1253])).

tff(c_1295,plain,(
    ! [B_334,A_335] :
      ( r1_tsep_1('#skF_4',B_334)
      | ~ m1_pre_topc(B_334,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_335)
      | ~ m1_pre_topc('#skF_2',A_335)
      | ~ m1_pre_topc(B_334,A_335)
      | v2_struct_0(B_334)
      | ~ l1_pre_topc(A_335)
      | ~ v2_pre_topc(A_335)
      | v2_struct_0(A_335) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_24,c_1261])).

tff(c_1297,plain,(
    ! [B_334] :
      ( r1_tsep_1('#skF_4',B_334)
      | ~ m1_pre_topc(B_334,'#skF_2')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_334,'#skF_1')
      | v2_struct_0(B_334)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_1295])).

tff(c_1300,plain,(
    ! [B_334] :
      ( r1_tsep_1('#skF_4',B_334)
      | ~ m1_pre_topc(B_334,'#skF_2')
      | ~ m1_pre_topc(B_334,'#skF_1')
      | v2_struct_0(B_334)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_1297])).

tff(c_1302,plain,(
    ! [B_336] :
      ( r1_tsep_1('#skF_4',B_336)
      | ~ m1_pre_topc(B_336,'#skF_2')
      | ~ m1_pre_topc(B_336,'#skF_1')
      | v2_struct_0(B_336) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1300])).

tff(c_1178,plain,(
    ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_1329,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1302,c_1178])).

tff(c_1362,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1329])).

tff(c_1365,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_1362])).

tff(c_1368,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_1365])).

tff(c_1370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_1368])).

tff(c_1371,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1329])).

tff(c_1373,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1371])).

tff(c_1387,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1373])).

tff(c_1390,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_1387])).

tff(c_1392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_1390])).

tff(c_1393,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1371])).

tff(c_1431,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1393,c_6])).

tff(c_1434,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_1431])).

tff(c_1436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_1434])).

tff(c_1438,plain,(
    r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1438,c_1033,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:36:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.21/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.77  
% 4.46/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.77  %$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.47/1.77  
% 4.47/1.77  %Foreground sorts:
% 4.47/1.77  
% 4.47/1.77  
% 4.47/1.77  %Background operators:
% 4.47/1.77  
% 4.47/1.77  
% 4.47/1.77  %Foreground operators:
% 4.47/1.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.47/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.47/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.47/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.47/1.77  tff('#skF_1', type, '#skF_1': $i).
% 4.47/1.77  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.47/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.47/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.77  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.47/1.77  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 4.47/1.77  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.47/1.77  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 4.47/1.77  
% 4.62/1.81  tff(f_157, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(B, C) => ((~r1_tsep_1(k2_tsep_1(A, B, C), D) => (~r1_tsep_1(B, D) & ~r1_tsep_1(C, D))) & (~r1_tsep_1(D, k2_tsep_1(A, B, C)) => (~r1_tsep_1(D, B) & ~r1_tsep_1(D, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tmap_1)).
% 4.62/1.81  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (m1_pre_topc(k2_tsep_1(A, B, C), B) & m1_pre_topc(k2_tsep_1(A, B, C), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tsep_1)).
% 4.62/1.81  tff(f_47, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 4.62/1.81  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 4.62/1.81  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.62/1.81  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.62/1.81  tff(c_28, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.62/1.81  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.62/1.81  tff(c_30, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.62/1.81  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.62/1.81  tff(c_20, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.62/1.81  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.62/1.81  tff(c_18, plain, (![A_19, B_23, C_25]: (m1_pre_topc(k2_tsep_1(A_19, B_23, C_25), B_23) | r1_tsep_1(B_23, C_25) | ~m1_pre_topc(C_25, A_19) | v2_struct_0(C_25) | ~m1_pre_topc(B_23, A_19) | v2_struct_0(B_23) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.62/1.81  tff(c_2, plain, (![A_1, B_2, C_3]: (m1_pre_topc(k2_tsep_1(A_1, B_2, C_3), A_1) | ~m1_pre_topc(C_3, A_1) | v2_struct_0(C_3) | ~m1_pre_topc(B_2, A_1) | v2_struct_0(B_2) | ~l1_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.62/1.81  tff(c_22, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.62/1.81  tff(c_24, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.62/1.81  tff(c_16, plain, (![A_19, B_23, C_25]: (m1_pre_topc(k2_tsep_1(A_19, B_23, C_25), C_25) | r1_tsep_1(B_23, C_25) | ~m1_pre_topc(C_25, A_19) | v2_struct_0(C_25) | ~m1_pre_topc(B_23, A_19) | v2_struct_0(B_23) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.62/1.81  tff(c_40, plain, (r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.62/1.81  tff(c_49, plain, (r1_tsep_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 4.62/1.81  tff(c_55, plain, (![D_52, B_53, C_54, A_55]: (r1_tsep_1(D_52, B_53) | ~r1_tsep_1(D_52, C_54) | ~m1_pre_topc(B_53, C_54) | ~m1_pre_topc(D_52, A_55) | v2_struct_0(D_52) | ~m1_pre_topc(C_54, A_55) | v2_struct_0(C_54) | ~m1_pre_topc(B_53, A_55) | v2_struct_0(B_53) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.62/1.81  tff(c_57, plain, (![B_53, A_55]: (r1_tsep_1('#skF_4', B_53) | ~m1_pre_topc(B_53, '#skF_2') | ~m1_pre_topc('#skF_4', A_55) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', A_55) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_53, A_55) | v2_struct_0(B_53) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(resolution, [status(thm)], [c_49, c_55])).
% 4.62/1.81  tff(c_61, plain, (![B_56, A_57]: (r1_tsep_1('#skF_4', B_56) | ~m1_pre_topc(B_56, '#skF_2') | ~m1_pre_topc('#skF_4', A_57) | ~m1_pre_topc('#skF_2', A_57) | ~m1_pre_topc(B_56, A_57) | v2_struct_0(B_56) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(negUnitSimplification, [status(thm)], [c_32, c_24, c_57])).
% 4.62/1.81  tff(c_63, plain, (![B_56]: (r1_tsep_1('#skF_4', B_56) | ~m1_pre_topc(B_56, '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_56, '#skF_1') | v2_struct_0(B_56) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_61])).
% 4.62/1.81  tff(c_66, plain, (![B_56]: (r1_tsep_1('#skF_4', B_56) | ~m1_pre_topc(B_56, '#skF_2') | ~m1_pre_topc(B_56, '#skF_1') | v2_struct_0(B_56) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_63])).
% 4.62/1.81  tff(c_68, plain, (![B_58]: (r1_tsep_1('#skF_4', B_58) | ~m1_pre_topc(B_58, '#skF_2') | ~m1_pre_topc(B_58, '#skF_1') | v2_struct_0(B_58))), inference(negUnitSimplification, [status(thm)], [c_38, c_66])).
% 4.62/1.81  tff(c_44, plain, (r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_2', '#skF_4') | ~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.62/1.81  tff(c_48, plain, (~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_44])).
% 4.62/1.81  tff(c_77, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_48])).
% 4.62/1.81  tff(c_89, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_77])).
% 4.62/1.81  tff(c_92, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_89])).
% 4.62/1.81  tff(c_95, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_92])).
% 4.62/1.81  tff(c_97, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_95])).
% 4.62/1.81  tff(c_98, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_77])).
% 4.62/1.81  tff(c_125, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_98])).
% 4.62/1.81  tff(c_128, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_125])).
% 4.62/1.81  tff(c_131, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_128])).
% 4.62/1.81  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_131])).
% 4.62/1.81  tff(c_134, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_98])).
% 4.62/1.81  tff(c_6, plain, (![A_1, B_2, C_3]: (~v2_struct_0(k2_tsep_1(A_1, B_2, C_3)) | ~m1_pre_topc(C_3, A_1) | v2_struct_0(C_3) | ~m1_pre_topc(B_2, A_1) | v2_struct_0(B_2) | ~l1_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.62/1.81  tff(c_138, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_134, c_6])).
% 4.62/1.81  tff(c_141, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_138])).
% 4.62/1.81  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_141])).
% 4.62/1.81  tff(c_144, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 4.62/1.81  tff(c_146, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_144])).
% 4.62/1.81  tff(c_158, plain, (![B_85, D_86, C_87, A_88]: (r1_tsep_1(B_85, D_86) | ~r1_tsep_1(C_87, D_86) | ~m1_pre_topc(B_85, C_87) | ~m1_pre_topc(D_86, A_88) | v2_struct_0(D_86) | ~m1_pre_topc(C_87, A_88) | v2_struct_0(C_87) | ~m1_pre_topc(B_85, A_88) | v2_struct_0(B_85) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.62/1.81  tff(c_160, plain, (![B_85, A_88]: (r1_tsep_1(B_85, '#skF_4') | ~m1_pre_topc(B_85, '#skF_3') | ~m1_pre_topc('#skF_4', A_88) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_88) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_85, A_88) | v2_struct_0(B_85) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | v2_struct_0(A_88))), inference(resolution, [status(thm)], [c_146, c_158])).
% 4.62/1.81  tff(c_182, plain, (![B_92, A_93]: (r1_tsep_1(B_92, '#skF_4') | ~m1_pre_topc(B_92, '#skF_3') | ~m1_pre_topc('#skF_4', A_93) | ~m1_pre_topc('#skF_3', A_93) | ~m1_pre_topc(B_92, A_93) | v2_struct_0(B_92) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(negUnitSimplification, [status(thm)], [c_28, c_24, c_160])).
% 4.62/1.81  tff(c_184, plain, (![B_92]: (r1_tsep_1(B_92, '#skF_4') | ~m1_pre_topc(B_92, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_92, '#skF_1') | v2_struct_0(B_92) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_182])).
% 4.62/1.81  tff(c_187, plain, (![B_92]: (r1_tsep_1(B_92, '#skF_4') | ~m1_pre_topc(B_92, '#skF_3') | ~m1_pre_topc(B_92, '#skF_1') | v2_struct_0(B_92) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_184])).
% 4.62/1.81  tff(c_189, plain, (![B_94]: (r1_tsep_1(B_94, '#skF_4') | ~m1_pre_topc(B_94, '#skF_3') | ~m1_pre_topc(B_94, '#skF_1') | v2_struct_0(B_94))), inference(negUnitSimplification, [status(thm)], [c_38, c_187])).
% 4.62/1.81  tff(c_42, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.62/1.81  tff(c_47, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_42])).
% 4.62/1.81  tff(c_203, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_189, c_47])).
% 4.62/1.81  tff(c_204, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_203])).
% 4.62/1.81  tff(c_207, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_204])).
% 4.62/1.81  tff(c_210, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_207])).
% 4.62/1.81  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_210])).
% 4.62/1.81  tff(c_213, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_203])).
% 4.62/1.81  tff(c_215, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_213])).
% 4.62/1.81  tff(c_218, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_215])).
% 4.62/1.81  tff(c_221, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_218])).
% 4.62/1.81  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_221])).
% 4.62/1.81  tff(c_224, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_213])).
% 4.62/1.81  tff(c_244, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_224, c_6])).
% 4.62/1.81  tff(c_247, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_244])).
% 4.62/1.81  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_247])).
% 4.62/1.81  tff(c_250, plain, (r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_144])).
% 4.62/1.81  tff(c_252, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_250])).
% 4.62/1.81  tff(c_320, plain, (![D_128, B_129, C_130, A_131]: (r1_tsep_1(D_128, B_129) | ~r1_tsep_1(D_128, C_130) | ~m1_pre_topc(B_129, C_130) | ~m1_pre_topc(D_128, A_131) | v2_struct_0(D_128) | ~m1_pre_topc(C_130, A_131) | v2_struct_0(C_130) | ~m1_pre_topc(B_129, A_131) | v2_struct_0(B_129) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.62/1.81  tff(c_326, plain, (![B_129, A_131]: (r1_tsep_1('#skF_4', B_129) | ~m1_pre_topc(B_129, '#skF_3') | ~m1_pre_topc('#skF_4', A_131) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_131) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_129, A_131) | v2_struct_0(B_129) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(resolution, [status(thm)], [c_252, c_320])).
% 4.62/1.81  tff(c_352, plain, (![B_136, A_137]: (r1_tsep_1('#skF_4', B_136) | ~m1_pre_topc(B_136, '#skF_3') | ~m1_pre_topc('#skF_4', A_137) | ~m1_pre_topc('#skF_3', A_137) | ~m1_pre_topc(B_136, A_137) | v2_struct_0(B_136) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137))), inference(negUnitSimplification, [status(thm)], [c_28, c_24, c_326])).
% 4.62/1.81  tff(c_354, plain, (![B_136]: (r1_tsep_1('#skF_4', B_136) | ~m1_pre_topc(B_136, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_136, '#skF_1') | v2_struct_0(B_136) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_352])).
% 4.62/1.81  tff(c_357, plain, (![B_136]: (r1_tsep_1('#skF_4', B_136) | ~m1_pre_topc(B_136, '#skF_3') | ~m1_pre_topc(B_136, '#skF_1') | v2_struct_0(B_136) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_354])).
% 4.62/1.81  tff(c_359, plain, (![B_138]: (r1_tsep_1('#skF_4', B_138) | ~m1_pre_topc(B_138, '#skF_3') | ~m1_pre_topc(B_138, '#skF_1') | v2_struct_0(B_138))), inference(negUnitSimplification, [status(thm)], [c_38, c_357])).
% 4.62/1.81  tff(c_390, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_359, c_48])).
% 4.62/1.81  tff(c_430, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_390])).
% 4.62/1.81  tff(c_433, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_430])).
% 4.62/1.81  tff(c_436, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_433])).
% 4.62/1.81  tff(c_438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_436])).
% 4.62/1.81  tff(c_439, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_390])).
% 4.62/1.81  tff(c_441, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_439])).
% 4.62/1.81  tff(c_444, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_441])).
% 4.62/1.81  tff(c_447, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_444])).
% 4.62/1.81  tff(c_449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_447])).
% 4.62/1.81  tff(c_450, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_439])).
% 4.62/1.81  tff(c_454, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_450, c_6])).
% 4.62/1.81  tff(c_457, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_454])).
% 4.62/1.81  tff(c_459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_457])).
% 4.62/1.81  tff(c_460, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_250])).
% 4.62/1.81  tff(c_467, plain, (![B_157, D_158, C_159, A_160]: (r1_tsep_1(B_157, D_158) | ~r1_tsep_1(C_159, D_158) | ~m1_pre_topc(B_157, C_159) | ~m1_pre_topc(D_158, A_160) | v2_struct_0(D_158) | ~m1_pre_topc(C_159, A_160) | v2_struct_0(C_159) | ~m1_pre_topc(B_157, A_160) | v2_struct_0(B_157) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.62/1.81  tff(c_469, plain, (![B_157, A_160]: (r1_tsep_1(B_157, '#skF_4') | ~m1_pre_topc(B_157, '#skF_2') | ~m1_pre_topc('#skF_4', A_160) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', A_160) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_157, A_160) | v2_struct_0(B_157) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(resolution, [status(thm)], [c_460, c_467])).
% 4.62/1.81  tff(c_473, plain, (![B_161, A_162]: (r1_tsep_1(B_161, '#skF_4') | ~m1_pre_topc(B_161, '#skF_2') | ~m1_pre_topc('#skF_4', A_162) | ~m1_pre_topc('#skF_2', A_162) | ~m1_pre_topc(B_161, A_162) | v2_struct_0(B_161) | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162) | v2_struct_0(A_162))), inference(negUnitSimplification, [status(thm)], [c_32, c_24, c_469])).
% 4.62/1.81  tff(c_475, plain, (![B_161]: (r1_tsep_1(B_161, '#skF_4') | ~m1_pre_topc(B_161, '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_161, '#skF_1') | v2_struct_0(B_161) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_473])).
% 4.62/1.81  tff(c_478, plain, (![B_161]: (r1_tsep_1(B_161, '#skF_4') | ~m1_pre_topc(B_161, '#skF_2') | ~m1_pre_topc(B_161, '#skF_1') | v2_struct_0(B_161) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_475])).
% 4.62/1.81  tff(c_480, plain, (![B_163]: (r1_tsep_1(B_163, '#skF_4') | ~m1_pre_topc(B_163, '#skF_2') | ~m1_pre_topc(B_163, '#skF_1') | v2_struct_0(B_163))), inference(negUnitSimplification, [status(thm)], [c_38, c_478])).
% 4.62/1.81  tff(c_496, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_480, c_47])).
% 4.62/1.81  tff(c_497, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_496])).
% 4.62/1.81  tff(c_500, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_497])).
% 4.62/1.81  tff(c_503, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_500])).
% 4.62/1.81  tff(c_505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_503])).
% 4.62/1.81  tff(c_506, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_496])).
% 4.62/1.81  tff(c_508, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_506])).
% 4.62/1.81  tff(c_511, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_508])).
% 4.62/1.81  tff(c_514, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_511])).
% 4.62/1.81  tff(c_516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_514])).
% 4.62/1.81  tff(c_517, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_506])).
% 4.62/1.81  tff(c_532, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_517, c_6])).
% 4.62/1.81  tff(c_535, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_532])).
% 4.62/1.81  tff(c_537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_535])).
% 4.62/1.81  tff(c_538, plain, (r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 4.62/1.81  tff(c_540, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_538])).
% 4.62/1.81  tff(c_614, plain, (![B_197, D_198, C_199, A_200]: (r1_tsep_1(B_197, D_198) | ~r1_tsep_1(C_199, D_198) | ~m1_pre_topc(B_197, C_199) | ~m1_pre_topc(D_198, A_200) | v2_struct_0(D_198) | ~m1_pre_topc(C_199, A_200) | v2_struct_0(C_199) | ~m1_pre_topc(B_197, A_200) | v2_struct_0(B_197) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200) | v2_struct_0(A_200))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.62/1.81  tff(c_622, plain, (![B_197, A_200]: (r1_tsep_1(B_197, '#skF_4') | ~m1_pre_topc(B_197, '#skF_3') | ~m1_pre_topc('#skF_4', A_200) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_200) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_197, A_200) | v2_struct_0(B_197) | ~l1_pre_topc(A_200) | ~v2_pre_topc(A_200) | v2_struct_0(A_200))), inference(resolution, [status(thm)], [c_540, c_614])).
% 4.62/1.81  tff(c_656, plain, (![B_205, A_206]: (r1_tsep_1(B_205, '#skF_4') | ~m1_pre_topc(B_205, '#skF_3') | ~m1_pre_topc('#skF_4', A_206) | ~m1_pre_topc('#skF_3', A_206) | ~m1_pre_topc(B_205, A_206) | v2_struct_0(B_205) | ~l1_pre_topc(A_206) | ~v2_pre_topc(A_206) | v2_struct_0(A_206))), inference(negUnitSimplification, [status(thm)], [c_28, c_24, c_622])).
% 4.62/1.81  tff(c_658, plain, (![B_205]: (r1_tsep_1(B_205, '#skF_4') | ~m1_pre_topc(B_205, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_205, '#skF_1') | v2_struct_0(B_205) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_656])).
% 4.62/1.81  tff(c_661, plain, (![B_205]: (r1_tsep_1(B_205, '#skF_4') | ~m1_pre_topc(B_205, '#skF_3') | ~m1_pre_topc(B_205, '#skF_1') | v2_struct_0(B_205) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_658])).
% 4.62/1.81  tff(c_663, plain, (![B_207]: (r1_tsep_1(B_207, '#skF_4') | ~m1_pre_topc(B_207, '#skF_3') | ~m1_pre_topc(B_207, '#skF_1') | v2_struct_0(B_207))), inference(negUnitSimplification, [status(thm)], [c_38, c_661])).
% 4.62/1.81  tff(c_687, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_663, c_47])).
% 4.62/1.81  tff(c_688, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_687])).
% 4.62/1.81  tff(c_698, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_688])).
% 4.62/1.81  tff(c_701, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_698])).
% 4.62/1.81  tff(c_703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_701])).
% 4.62/1.81  tff(c_704, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_687])).
% 4.62/1.81  tff(c_706, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_704])).
% 4.62/1.81  tff(c_709, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_706])).
% 4.62/1.81  tff(c_712, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_709])).
% 4.62/1.81  tff(c_714, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_712])).
% 4.62/1.81  tff(c_715, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_704])).
% 4.62/1.81  tff(c_719, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_715, c_6])).
% 4.62/1.81  tff(c_722, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_719])).
% 4.62/1.81  tff(c_724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_722])).
% 4.62/1.81  tff(c_725, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_538])).
% 4.62/1.81  tff(c_892, plain, (![B_252, D_253, C_254, A_255]: (r1_tsep_1(B_252, D_253) | ~r1_tsep_1(C_254, D_253) | ~m1_pre_topc(B_252, C_254) | ~m1_pre_topc(D_253, A_255) | v2_struct_0(D_253) | ~m1_pre_topc(C_254, A_255) | v2_struct_0(C_254) | ~m1_pre_topc(B_252, A_255) | v2_struct_0(B_252) | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255) | v2_struct_0(A_255))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.62/1.81  tff(c_902, plain, (![B_252, A_255]: (r1_tsep_1(B_252, '#skF_4') | ~m1_pre_topc(B_252, '#skF_2') | ~m1_pre_topc('#skF_4', A_255) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', A_255) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_252, A_255) | v2_struct_0(B_252) | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255) | v2_struct_0(A_255))), inference(resolution, [status(thm)], [c_725, c_892])).
% 4.62/1.81  tff(c_918, plain, (![B_256, A_257]: (r1_tsep_1(B_256, '#skF_4') | ~m1_pre_topc(B_256, '#skF_2') | ~m1_pre_topc('#skF_4', A_257) | ~m1_pre_topc('#skF_2', A_257) | ~m1_pre_topc(B_256, A_257) | v2_struct_0(B_256) | ~l1_pre_topc(A_257) | ~v2_pre_topc(A_257) | v2_struct_0(A_257))), inference(negUnitSimplification, [status(thm)], [c_32, c_24, c_902])).
% 4.62/1.81  tff(c_920, plain, (![B_256]: (r1_tsep_1(B_256, '#skF_4') | ~m1_pre_topc(B_256, '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_256, '#skF_1') | v2_struct_0(B_256) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_918])).
% 4.62/1.81  tff(c_923, plain, (![B_256]: (r1_tsep_1(B_256, '#skF_4') | ~m1_pre_topc(B_256, '#skF_2') | ~m1_pre_topc(B_256, '#skF_1') | v2_struct_0(B_256) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_920])).
% 4.62/1.81  tff(c_925, plain, (![B_258]: (r1_tsep_1(B_258, '#skF_4') | ~m1_pre_topc(B_258, '#skF_2') | ~m1_pre_topc(B_258, '#skF_1') | v2_struct_0(B_258))), inference(negUnitSimplification, [status(thm)], [c_38, c_923])).
% 4.62/1.81  tff(c_955, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_925, c_47])).
% 4.62/1.81  tff(c_956, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_955])).
% 4.62/1.81  tff(c_970, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_956])).
% 4.62/1.81  tff(c_973, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_970])).
% 4.62/1.81  tff(c_975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_973])).
% 4.62/1.81  tff(c_976, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_955])).
% 4.62/1.81  tff(c_1013, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_976])).
% 4.62/1.81  tff(c_1016, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1013])).
% 4.62/1.81  tff(c_1019, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_1016])).
% 4.62/1.81  tff(c_1021, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_1019])).
% 4.62/1.81  tff(c_1022, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_976])).
% 4.62/1.81  tff(c_1026, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1022, c_6])).
% 4.62/1.81  tff(c_1029, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_1026])).
% 4.62/1.81  tff(c_1031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_1029])).
% 4.62/1.81  tff(c_1032, plain, (r1_tsep_1('#skF_4', '#skF_2') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 4.62/1.81  tff(c_1034, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1032])).
% 4.62/1.81  tff(c_1075, plain, (![D_284, B_285, C_286, A_287]: (r1_tsep_1(D_284, B_285) | ~r1_tsep_1(D_284, C_286) | ~m1_pre_topc(B_285, C_286) | ~m1_pre_topc(D_284, A_287) | v2_struct_0(D_284) | ~m1_pre_topc(C_286, A_287) | v2_struct_0(C_286) | ~m1_pre_topc(B_285, A_287) | v2_struct_0(B_285) | ~l1_pre_topc(A_287) | ~v2_pre_topc(A_287) | v2_struct_0(A_287))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.62/1.81  tff(c_1081, plain, (![B_285, A_287]: (r1_tsep_1('#skF_4', B_285) | ~m1_pre_topc(B_285, '#skF_3') | ~m1_pre_topc('#skF_4', A_287) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_287) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_285, A_287) | v2_struct_0(B_285) | ~l1_pre_topc(A_287) | ~v2_pre_topc(A_287) | v2_struct_0(A_287))), inference(resolution, [status(thm)], [c_1034, c_1075])).
% 4.62/1.81  tff(c_1091, plain, (![B_288, A_289]: (r1_tsep_1('#skF_4', B_288) | ~m1_pre_topc(B_288, '#skF_3') | ~m1_pre_topc('#skF_4', A_289) | ~m1_pre_topc('#skF_3', A_289) | ~m1_pre_topc(B_288, A_289) | v2_struct_0(B_288) | ~l1_pre_topc(A_289) | ~v2_pre_topc(A_289) | v2_struct_0(A_289))), inference(negUnitSimplification, [status(thm)], [c_28, c_24, c_1081])).
% 4.62/1.81  tff(c_1093, plain, (![B_288]: (r1_tsep_1('#skF_4', B_288) | ~m1_pre_topc(B_288, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_288, '#skF_1') | v2_struct_0(B_288) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_1091])).
% 4.62/1.81  tff(c_1096, plain, (![B_288]: (r1_tsep_1('#skF_4', B_288) | ~m1_pre_topc(B_288, '#skF_3') | ~m1_pre_topc(B_288, '#skF_1') | v2_struct_0(B_288) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_1093])).
% 4.62/1.81  tff(c_1098, plain, (![B_290]: (r1_tsep_1('#skF_4', B_290) | ~m1_pre_topc(B_290, '#skF_3') | ~m1_pre_topc(B_290, '#skF_1') | v2_struct_0(B_290))), inference(negUnitSimplification, [status(thm)], [c_38, c_1096])).
% 4.62/1.81  tff(c_1035, plain, (~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_44])).
% 4.62/1.81  tff(c_1112, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1098, c_1035])).
% 4.62/1.81  tff(c_1113, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1112])).
% 4.62/1.81  tff(c_1116, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_1113])).
% 4.62/1.81  tff(c_1119, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_1116])).
% 4.62/1.81  tff(c_1121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_1119])).
% 4.62/1.81  tff(c_1122, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1112])).
% 4.62/1.81  tff(c_1145, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1122])).
% 4.62/1.81  tff(c_1148, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_1145])).
% 4.62/1.81  tff(c_1151, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_1148])).
% 4.62/1.81  tff(c_1153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_1151])).
% 4.62/1.81  tff(c_1154, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1122])).
% 4.62/1.81  tff(c_1165, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1154, c_6])).
% 4.62/1.81  tff(c_1168, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_1165])).
% 4.62/1.81  tff(c_1170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_1168])).
% 4.62/1.81  tff(c_1172, plain, (r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_44])).
% 4.62/1.81  tff(c_1033, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 4.62/1.81  tff(c_46, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.62/1.81  tff(c_1175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1172, c_1033, c_46])).
% 4.62/1.81  tff(c_1176, plain, (r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_1032])).
% 4.62/1.81  tff(c_1253, plain, (![D_326, B_327, C_328, A_329]: (r1_tsep_1(D_326, B_327) | ~r1_tsep_1(D_326, C_328) | ~m1_pre_topc(B_327, C_328) | ~m1_pre_topc(D_326, A_329) | v2_struct_0(D_326) | ~m1_pre_topc(C_328, A_329) | v2_struct_0(C_328) | ~m1_pre_topc(B_327, A_329) | v2_struct_0(B_327) | ~l1_pre_topc(A_329) | ~v2_pre_topc(A_329) | v2_struct_0(A_329))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.62/1.81  tff(c_1261, plain, (![B_327, A_329]: (r1_tsep_1('#skF_4', B_327) | ~m1_pre_topc(B_327, '#skF_2') | ~m1_pre_topc('#skF_4', A_329) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', A_329) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_327, A_329) | v2_struct_0(B_327) | ~l1_pre_topc(A_329) | ~v2_pre_topc(A_329) | v2_struct_0(A_329))), inference(resolution, [status(thm)], [c_1176, c_1253])).
% 4.62/1.81  tff(c_1295, plain, (![B_334, A_335]: (r1_tsep_1('#skF_4', B_334) | ~m1_pre_topc(B_334, '#skF_2') | ~m1_pre_topc('#skF_4', A_335) | ~m1_pre_topc('#skF_2', A_335) | ~m1_pre_topc(B_334, A_335) | v2_struct_0(B_334) | ~l1_pre_topc(A_335) | ~v2_pre_topc(A_335) | v2_struct_0(A_335))), inference(negUnitSimplification, [status(thm)], [c_32, c_24, c_1261])).
% 4.62/1.81  tff(c_1297, plain, (![B_334]: (r1_tsep_1('#skF_4', B_334) | ~m1_pre_topc(B_334, '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_334, '#skF_1') | v2_struct_0(B_334) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_1295])).
% 4.62/1.81  tff(c_1300, plain, (![B_334]: (r1_tsep_1('#skF_4', B_334) | ~m1_pre_topc(B_334, '#skF_2') | ~m1_pre_topc(B_334, '#skF_1') | v2_struct_0(B_334) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_1297])).
% 4.62/1.81  tff(c_1302, plain, (![B_336]: (r1_tsep_1('#skF_4', B_336) | ~m1_pre_topc(B_336, '#skF_2') | ~m1_pre_topc(B_336, '#skF_1') | v2_struct_0(B_336))), inference(negUnitSimplification, [status(thm)], [c_38, c_1300])).
% 4.62/1.81  tff(c_1178, plain, (~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_44])).
% 4.62/1.81  tff(c_1329, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1302, c_1178])).
% 4.62/1.81  tff(c_1362, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1329])).
% 4.62/1.81  tff(c_1365, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_1362])).
% 4.62/1.81  tff(c_1368, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_1365])).
% 4.62/1.81  tff(c_1370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_1368])).
% 4.62/1.81  tff(c_1371, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1329])).
% 4.62/1.81  tff(c_1373, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1371])).
% 4.62/1.81  tff(c_1387, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1373])).
% 4.62/1.81  tff(c_1390, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_1387])).
% 4.62/1.81  tff(c_1392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_1390])).
% 4.62/1.81  tff(c_1393, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1371])).
% 4.62/1.81  tff(c_1431, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1393, c_6])).
% 4.62/1.81  tff(c_1434, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_1431])).
% 4.62/1.81  tff(c_1436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_1434])).
% 4.62/1.81  tff(c_1438, plain, (r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_44])).
% 4.62/1.81  tff(c_1443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1438, c_1033, c_46])).
% 4.62/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.81  
% 4.62/1.81  Inference rules
% 4.62/1.81  ----------------------
% 4.62/1.81  #Ref     : 0
% 4.62/1.81  #Sup     : 218
% 4.62/1.81  #Fact    : 0
% 4.62/1.81  #Define  : 0
% 4.62/1.81  #Split   : 30
% 4.62/1.81  #Chain   : 0
% 4.62/1.81  #Close   : 0
% 4.62/1.81  
% 4.62/1.81  Ordering : KBO
% 4.62/1.81  
% 4.62/1.81  Simplification rules
% 4.62/1.81  ----------------------
% 4.62/1.81  #Subsume      : 22
% 4.62/1.81  #Demod        : 201
% 4.62/1.81  #Tautology    : 6
% 4.62/1.81  #SimpNegUnit  : 200
% 4.62/1.81  #BackRed      : 0
% 4.62/1.81  
% 4.62/1.81  #Partial instantiations: 0
% 4.62/1.81  #Strategies tried      : 1
% 4.62/1.81  
% 4.62/1.81  Timing (in seconds)
% 4.62/1.81  ----------------------
% 4.62/1.81  Preprocessing        : 0.29
% 4.62/1.81  Parsing              : 0.15
% 4.62/1.81  CNF conversion       : 0.02
% 4.62/1.81  Main loop            : 0.66
% 4.62/1.81  Inferencing          : 0.22
% 4.62/1.81  Reduction            : 0.16
% 4.62/1.81  Demodulation         : 0.10
% 4.62/1.81  BG Simplification    : 0.03
% 4.62/1.81  Subsumption          : 0.21
% 4.62/1.81  Abstraction          : 0.03
% 4.62/1.81  MUC search           : 0.00
% 4.62/1.81  Cooper               : 0.00
% 4.62/1.81  Total                : 1.01
% 4.62/1.81  Index Insertion      : 0.00
% 4.62/1.81  Index Deletion       : 0.00
% 4.62/1.81  Index Matching       : 0.00
% 4.62/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
