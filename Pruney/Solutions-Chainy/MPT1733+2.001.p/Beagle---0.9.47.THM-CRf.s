%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:47 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :  217 (1209 expanded)
%              Number of leaves         :   18 ( 443 expanded)
%              Depth                    :   15
%              Number of atoms          :  849 (9019 expanded)
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

tff(f_151,negated_conjecture,(
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
                     => ( ( ( r1_tsep_1(B,D)
                            | r1_tsep_1(C,D) )
                         => r1_tsep_1(k2_tsep_1(A,B,C),D) )
                        & ( ( r1_tsep_1(D,B)
                            | r1_tsep_1(D,C) )
                         => r1_tsep_1(D,k2_tsep_1(A,B,C)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tmap_1)).

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
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_30,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_20,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

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
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

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

tff(c_46,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_49,plain,(
    r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

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

tff(c_42,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_2','#skF_4')
    | ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_47,plain,(
    ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_77,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_47])).

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
    inference(splitRight,[status(thm)],[c_46])).

tff(c_146,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_207,plain,(
    ! [B_95,D_96,C_97,A_98] :
      ( r1_tsep_1(B_95,D_96)
      | ~ r1_tsep_1(C_97,D_96)
      | ~ m1_pre_topc(B_95,C_97)
      | ~ m1_pre_topc(D_96,A_98)
      | v2_struct_0(D_96)
      | ~ m1_pre_topc(C_97,A_98)
      | v2_struct_0(C_97)
      | ~ m1_pre_topc(B_95,A_98)
      | v2_struct_0(B_95)
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_213,plain,(
    ! [B_95,A_98] :
      ( r1_tsep_1(B_95,'#skF_4')
      | ~ m1_pre_topc(B_95,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_98)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_98)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_95,A_98)
      | v2_struct_0(B_95)
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_146,c_207])).

tff(c_223,plain,(
    ! [B_99,A_100] :
      ( r1_tsep_1(B_99,'#skF_4')
      | ~ m1_pre_topc(B_99,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_100)
      | ~ m1_pre_topc('#skF_3',A_100)
      | ~ m1_pre_topc(B_99,A_100)
      | v2_struct_0(B_99)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_24,c_213])).

tff(c_225,plain,(
    ! [B_99] :
      ( r1_tsep_1(B_99,'#skF_4')
      | ~ m1_pre_topc(B_99,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_99,'#skF_1')
      | v2_struct_0(B_99)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_223])).

tff(c_228,plain,(
    ! [B_99] :
      ( r1_tsep_1(B_99,'#skF_4')
      | ~ m1_pre_topc(B_99,'#skF_3')
      | ~ m1_pre_topc(B_99,'#skF_1')
      | v2_struct_0(B_99)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_225])).

tff(c_230,plain,(
    ! [B_101] :
      ( r1_tsep_1(B_101,'#skF_4')
      | ~ m1_pre_topc(B_101,'#skF_3')
      | ~ m1_pre_topc(B_101,'#skF_1')
      | v2_struct_0(B_101) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_228])).

tff(c_44,plain,
    ( ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_48,plain,(
    ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_249,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_230,c_48])).

tff(c_250,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_253,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_250])).

tff(c_256,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_253])).

tff(c_258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_256])).

tff(c_259,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_282,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_285,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_282])).

tff(c_288,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_285])).

tff(c_290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_288])).

tff(c_291,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_302,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_291,c_6])).

tff(c_305,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_302])).

tff(c_307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_305])).

tff(c_308,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_310,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_316,plain,(
    ! [B_123,D_124,C_125,A_126] :
      ( r1_tsep_1(B_123,D_124)
      | ~ r1_tsep_1(D_124,C_125)
      | ~ m1_pre_topc(B_123,C_125)
      | ~ m1_pre_topc(D_124,A_126)
      | v2_struct_0(D_124)
      | ~ m1_pre_topc(C_125,A_126)
      | v2_struct_0(C_125)
      | ~ m1_pre_topc(B_123,A_126)
      | v2_struct_0(B_123)
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_318,plain,(
    ! [B_123,A_126] :
      ( r1_tsep_1(B_123,'#skF_4')
      | ~ m1_pre_topc(B_123,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_126)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_126)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_123,A_126)
      | v2_struct_0(B_123)
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(resolution,[status(thm)],[c_310,c_316])).

tff(c_322,plain,(
    ! [B_127,A_128] :
      ( r1_tsep_1(B_127,'#skF_4')
      | ~ m1_pre_topc(B_127,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_128)
      | ~ m1_pre_topc('#skF_3',A_128)
      | ~ m1_pre_topc(B_127,A_128)
      | v2_struct_0(B_127)
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128)
      | v2_struct_0(A_128) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_24,c_318])).

tff(c_324,plain,(
    ! [B_127] :
      ( r1_tsep_1(B_127,'#skF_4')
      | ~ m1_pre_topc(B_127,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_127,'#skF_1')
      | v2_struct_0(B_127)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_322])).

tff(c_327,plain,(
    ! [B_127] :
      ( r1_tsep_1(B_127,'#skF_4')
      | ~ m1_pre_topc(B_127,'#skF_3')
      | ~ m1_pre_topc(B_127,'#skF_1')
      | v2_struct_0(B_127)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_324])).

tff(c_329,plain,(
    ! [B_129] :
      ( r1_tsep_1(B_129,'#skF_4')
      | ~ m1_pre_topc(B_129,'#skF_3')
      | ~ m1_pre_topc(B_129,'#skF_1')
      | v2_struct_0(B_129) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_327])).

tff(c_345,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_329,c_48])).

tff(c_346,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_349,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_346])).

tff(c_352,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_349])).

tff(c_354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_352])).

tff(c_355,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_368,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_355])).

tff(c_371,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_368])).

tff(c_374,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_371])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_374])).

tff(c_377,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_388,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_377,c_6])).

tff(c_391,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_388])).

tff(c_393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_391])).

tff(c_394,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_463,plain,(
    ! [B_165,D_166,C_167,A_168] :
      ( r1_tsep_1(B_165,D_166)
      | ~ r1_tsep_1(C_167,D_166)
      | ~ m1_pre_topc(B_165,C_167)
      | ~ m1_pre_topc(D_166,A_168)
      | v2_struct_0(D_166)
      | ~ m1_pre_topc(C_167,A_168)
      | v2_struct_0(C_167)
      | ~ m1_pre_topc(B_165,A_168)
      | v2_struct_0(B_165)
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_469,plain,(
    ! [B_165,A_168] :
      ( r1_tsep_1(B_165,'#skF_4')
      | ~ m1_pre_topc(B_165,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_168)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2',A_168)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_165,A_168)
      | v2_struct_0(B_165)
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_394,c_463])).

tff(c_479,plain,(
    ! [B_169,A_170] :
      ( r1_tsep_1(B_169,'#skF_4')
      | ~ m1_pre_topc(B_169,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_170)
      | ~ m1_pre_topc('#skF_2',A_170)
      | ~ m1_pre_topc(B_169,A_170)
      | v2_struct_0(B_169)
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_24,c_469])).

tff(c_481,plain,(
    ! [B_169] :
      ( r1_tsep_1(B_169,'#skF_4')
      | ~ m1_pre_topc(B_169,'#skF_2')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_169,'#skF_1')
      | v2_struct_0(B_169)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_479])).

tff(c_484,plain,(
    ! [B_169] :
      ( r1_tsep_1(B_169,'#skF_4')
      | ~ m1_pre_topc(B_169,'#skF_2')
      | ~ m1_pre_topc(B_169,'#skF_1')
      | v2_struct_0(B_169)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_481])).

tff(c_486,plain,(
    ! [B_171] :
      ( r1_tsep_1(B_171,'#skF_4')
      | ~ m1_pre_topc(B_171,'#skF_2')
      | ~ m1_pre_topc(B_171,'#skF_1')
      | v2_struct_0(B_171) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_484])).

tff(c_512,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_486,c_48])).

tff(c_513,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_512])).

tff(c_516,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_513])).

tff(c_519,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_516])).

tff(c_521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_519])).

tff(c_522,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_512])).

tff(c_524,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_522])).

tff(c_527,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_524])).

tff(c_530,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_527])).

tff(c_532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_530])).

tff(c_533,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_522])).

tff(c_558,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_533,c_6])).

tff(c_561,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_558])).

tff(c_563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_561])).

tff(c_564,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_566,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_564])).

tff(c_573,plain,(
    ! [D_191,B_192,C_193,A_194] :
      ( r1_tsep_1(D_191,B_192)
      | ~ r1_tsep_1(D_191,C_193)
      | ~ m1_pre_topc(B_192,C_193)
      | ~ m1_pre_topc(D_191,A_194)
      | v2_struct_0(D_191)
      | ~ m1_pre_topc(C_193,A_194)
      | v2_struct_0(C_193)
      | ~ m1_pre_topc(B_192,A_194)
      | v2_struct_0(B_192)
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_577,plain,(
    ! [B_192,A_194] :
      ( r1_tsep_1('#skF_4',B_192)
      | ~ m1_pre_topc(B_192,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_194)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_194)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_192,A_194)
      | v2_struct_0(B_192)
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(resolution,[status(thm)],[c_566,c_573])).

tff(c_584,plain,(
    ! [B_195,A_196] :
      ( r1_tsep_1('#skF_4',B_195)
      | ~ m1_pre_topc(B_195,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_196)
      | ~ m1_pre_topc('#skF_3',A_196)
      | ~ m1_pre_topc(B_195,A_196)
      | v2_struct_0(B_195)
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196)
      | v2_struct_0(A_196) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_24,c_577])).

tff(c_586,plain,(
    ! [B_195] :
      ( r1_tsep_1('#skF_4',B_195)
      | ~ m1_pre_topc(B_195,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_195,'#skF_1')
      | v2_struct_0(B_195)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_584])).

tff(c_589,plain,(
    ! [B_195] :
      ( r1_tsep_1('#skF_4',B_195)
      | ~ m1_pre_topc(B_195,'#skF_3')
      | ~ m1_pre_topc(B_195,'#skF_1')
      | v2_struct_0(B_195)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_586])).

tff(c_591,plain,(
    ! [B_197] :
      ( r1_tsep_1('#skF_4',B_197)
      | ~ m1_pre_topc(B_197,'#skF_3')
      | ~ m1_pre_topc(B_197,'#skF_1')
      | v2_struct_0(B_197) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_589])).

tff(c_600,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_591,c_47])).

tff(c_601,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_600])).

tff(c_604,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_601])).

tff(c_607,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_604])).

tff(c_609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_607])).

tff(c_610,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_600])).

tff(c_612,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_610])).

tff(c_615,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_612])).

tff(c_618,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_615])).

tff(c_620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_618])).

tff(c_621,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_610])).

tff(c_641,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_621,c_6])).

tff(c_644,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_641])).

tff(c_646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_644])).

tff(c_647,plain,(
    r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_564])).

tff(c_656,plain,(
    ! [D_217,B_218,C_219,A_220] :
      ( r1_tsep_1(D_217,B_218)
      | ~ r1_tsep_1(D_217,C_219)
      | ~ m1_pre_topc(B_218,C_219)
      | ~ m1_pre_topc(D_217,A_220)
      | v2_struct_0(D_217)
      | ~ m1_pre_topc(C_219,A_220)
      | v2_struct_0(C_219)
      | ~ m1_pre_topc(B_218,A_220)
      | v2_struct_0(B_218)
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_660,plain,(
    ! [B_218,A_220] :
      ( r1_tsep_1('#skF_4',B_218)
      | ~ m1_pre_topc(B_218,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_220)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2',A_220)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_218,A_220)
      | v2_struct_0(B_218)
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(resolution,[status(thm)],[c_647,c_656])).

tff(c_667,plain,(
    ! [B_221,A_222] :
      ( r1_tsep_1('#skF_4',B_221)
      | ~ m1_pre_topc(B_221,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_222)
      | ~ m1_pre_topc('#skF_2',A_222)
      | ~ m1_pre_topc(B_221,A_222)
      | v2_struct_0(B_221)
      | ~ l1_pre_topc(A_222)
      | ~ v2_pre_topc(A_222)
      | v2_struct_0(A_222) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_24,c_660])).

tff(c_669,plain,(
    ! [B_221] :
      ( r1_tsep_1('#skF_4',B_221)
      | ~ m1_pre_topc(B_221,'#skF_2')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_221,'#skF_1')
      | v2_struct_0(B_221)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_667])).

tff(c_672,plain,(
    ! [B_221] :
      ( r1_tsep_1('#skF_4',B_221)
      | ~ m1_pre_topc(B_221,'#skF_2')
      | ~ m1_pre_topc(B_221,'#skF_1')
      | v2_struct_0(B_221)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_669])).

tff(c_674,plain,(
    ! [B_223] :
      ( r1_tsep_1('#skF_4',B_223)
      | ~ m1_pre_topc(B_223,'#skF_2')
      | ~ m1_pre_topc(B_223,'#skF_1')
      | v2_struct_0(B_223) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_672])).

tff(c_690,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_674,c_47])).

tff(c_691,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_690])).

tff(c_694,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_691])).

tff(c_697,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_694])).

tff(c_699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_697])).

tff(c_700,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_690])).

tff(c_702,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_700])).

tff(c_721,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_702])).

tff(c_724,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_721])).

tff(c_726,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_724])).

tff(c_727,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_700])).

tff(c_731,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_727,c_6])).

tff(c_734,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_731])).

tff(c_736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_734])).

tff(c_738,plain,(
    r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_737,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_739,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_737])).

tff(c_861,plain,(
    ! [B_264,D_265,C_266,A_267] :
      ( r1_tsep_1(B_264,D_265)
      | ~ r1_tsep_1(C_266,D_265)
      | ~ m1_pre_topc(B_264,C_266)
      | ~ m1_pre_topc(D_265,A_267)
      | v2_struct_0(D_265)
      | ~ m1_pre_topc(C_266,A_267)
      | v2_struct_0(C_266)
      | ~ m1_pre_topc(B_264,A_267)
      | v2_struct_0(B_264)
      | ~ l1_pre_topc(A_267)
      | ~ v2_pre_topc(A_267)
      | v2_struct_0(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_871,plain,(
    ! [B_264,A_267] :
      ( r1_tsep_1(B_264,'#skF_4')
      | ~ m1_pre_topc(B_264,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_267)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_267)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_264,A_267)
      | v2_struct_0(B_264)
      | ~ l1_pre_topc(A_267)
      | ~ v2_pre_topc(A_267)
      | v2_struct_0(A_267) ) ),
    inference(resolution,[status(thm)],[c_739,c_861])).

tff(c_887,plain,(
    ! [B_268,A_269] :
      ( r1_tsep_1(B_268,'#skF_4')
      | ~ m1_pre_topc(B_268,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_269)
      | ~ m1_pre_topc('#skF_3',A_269)
      | ~ m1_pre_topc(B_268,A_269)
      | v2_struct_0(B_268)
      | ~ l1_pre_topc(A_269)
      | ~ v2_pre_topc(A_269)
      | v2_struct_0(A_269) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_24,c_871])).

tff(c_889,plain,(
    ! [B_268] :
      ( r1_tsep_1(B_268,'#skF_4')
      | ~ m1_pre_topc(B_268,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_268,'#skF_1')
      | v2_struct_0(B_268)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_887])).

tff(c_892,plain,(
    ! [B_268] :
      ( r1_tsep_1(B_268,'#skF_4')
      | ~ m1_pre_topc(B_268,'#skF_3')
      | ~ m1_pre_topc(B_268,'#skF_1')
      | v2_struct_0(B_268)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_889])).

tff(c_894,plain,(
    ! [B_270] :
      ( r1_tsep_1(B_270,'#skF_4')
      | ~ m1_pre_topc(B_270,'#skF_3')
      | ~ m1_pre_topc(B_270,'#skF_1')
      | v2_struct_0(B_270) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_892])).

tff(c_40,plain,
    ( ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_740,plain,(
    ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_742,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_740])).

tff(c_743,plain,(
    ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_918,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_894,c_743])).

tff(c_919,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_918])).

tff(c_922,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_919])).

tff(c_925,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_922])).

tff(c_927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_925])).

tff(c_928,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_918])).

tff(c_964,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_928])).

tff(c_967,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_964])).

tff(c_970,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_967])).

tff(c_972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_970])).

tff(c_973,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_928])).

tff(c_977,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_973,c_6])).

tff(c_980,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_977])).

tff(c_982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_980])).

tff(c_983,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_737])).

tff(c_995,plain,(
    ! [B_289,D_290,C_291,A_292] :
      ( r1_tsep_1(B_289,D_290)
      | ~ r1_tsep_1(C_291,D_290)
      | ~ m1_pre_topc(B_289,C_291)
      | ~ m1_pre_topc(D_290,A_292)
      | v2_struct_0(D_290)
      | ~ m1_pre_topc(C_291,A_292)
      | v2_struct_0(C_291)
      | ~ m1_pre_topc(B_289,A_292)
      | v2_struct_0(B_289)
      | ~ l1_pre_topc(A_292)
      | ~ v2_pre_topc(A_292)
      | v2_struct_0(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_999,plain,(
    ! [B_289,A_292] :
      ( r1_tsep_1(B_289,'#skF_4')
      | ~ m1_pre_topc(B_289,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_292)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2',A_292)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_289,A_292)
      | v2_struct_0(B_289)
      | ~ l1_pre_topc(A_292)
      | ~ v2_pre_topc(A_292)
      | v2_struct_0(A_292) ) ),
    inference(resolution,[status(thm)],[c_983,c_995])).

tff(c_1006,plain,(
    ! [B_293,A_294] :
      ( r1_tsep_1(B_293,'#skF_4')
      | ~ m1_pre_topc(B_293,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_294)
      | ~ m1_pre_topc('#skF_2',A_294)
      | ~ m1_pre_topc(B_293,A_294)
      | v2_struct_0(B_293)
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294)
      | v2_struct_0(A_294) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_24,c_999])).

tff(c_1008,plain,(
    ! [B_293] :
      ( r1_tsep_1(B_293,'#skF_4')
      | ~ m1_pre_topc(B_293,'#skF_2')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_293,'#skF_1')
      | v2_struct_0(B_293)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_1006])).

tff(c_1011,plain,(
    ! [B_293] :
      ( r1_tsep_1(B_293,'#skF_4')
      | ~ m1_pre_topc(B_293,'#skF_2')
      | ~ m1_pre_topc(B_293,'#skF_1')
      | v2_struct_0(B_293)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_1008])).

tff(c_1013,plain,(
    ! [B_295] :
      ( r1_tsep_1(B_295,'#skF_4')
      | ~ m1_pre_topc(B_295,'#skF_2')
      | ~ m1_pre_topc(B_295,'#skF_1')
      | v2_struct_0(B_295) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1011])).

tff(c_985,plain,(
    ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_1025,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1013,c_985])).

tff(c_1030,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1025])).

tff(c_1033,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_1030])).

tff(c_1036,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_1033])).

tff(c_1038,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_1036])).

tff(c_1039,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1025])).

tff(c_1041,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1039])).

tff(c_1044,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1041])).

tff(c_1047,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_1044])).

tff(c_1049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_1047])).

tff(c_1050,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1039])).

tff(c_1070,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1050,c_6])).

tff(c_1073,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_1070])).

tff(c_1075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_1073])).

tff(c_1077,plain,(
    r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_1077,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.63  
% 3.75/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.63  %$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.75/1.63  
% 3.75/1.63  %Foreground sorts:
% 3.75/1.63  
% 3.75/1.63  
% 3.75/1.63  %Background operators:
% 3.75/1.63  
% 3.75/1.63  
% 3.75/1.63  %Foreground operators:
% 3.75/1.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.75/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.75/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.75/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.75/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.75/1.63  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.75/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.75/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.63  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.75/1.63  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 3.75/1.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.75/1.63  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.75/1.63  
% 4.09/1.66  tff(f_151, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(B, C) => (((r1_tsep_1(B, D) | r1_tsep_1(C, D)) => r1_tsep_1(k2_tsep_1(A, B, C), D)) & ((r1_tsep_1(D, B) | r1_tsep_1(D, C)) => r1_tsep_1(D, k2_tsep_1(A, B, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tmap_1)).
% 4.09/1.66  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (m1_pre_topc(k2_tsep_1(A, B, C), B) & m1_pre_topc(k2_tsep_1(A, B, C), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tsep_1)).
% 4.09/1.66  tff(f_47, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 4.09/1.66  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 4.09/1.66  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.09/1.66  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.09/1.66  tff(c_28, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.09/1.66  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.09/1.66  tff(c_30, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.09/1.66  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.09/1.66  tff(c_20, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.09/1.66  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.09/1.66  tff(c_18, plain, (![A_19, B_23, C_25]: (m1_pre_topc(k2_tsep_1(A_19, B_23, C_25), B_23) | r1_tsep_1(B_23, C_25) | ~m1_pre_topc(C_25, A_19) | v2_struct_0(C_25) | ~m1_pre_topc(B_23, A_19) | v2_struct_0(B_23) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.09/1.66  tff(c_2, plain, (![A_1, B_2, C_3]: (m1_pre_topc(k2_tsep_1(A_1, B_2, C_3), A_1) | ~m1_pre_topc(C_3, A_1) | v2_struct_0(C_3) | ~m1_pre_topc(B_2, A_1) | v2_struct_0(B_2) | ~l1_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.09/1.66  tff(c_22, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.09/1.66  tff(c_24, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.09/1.66  tff(c_16, plain, (![A_19, B_23, C_25]: (m1_pre_topc(k2_tsep_1(A_19, B_23, C_25), C_25) | r1_tsep_1(B_23, C_25) | ~m1_pre_topc(C_25, A_19) | v2_struct_0(C_25) | ~m1_pre_topc(B_23, A_19) | v2_struct_0(B_23) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.09/1.66  tff(c_46, plain, (r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.09/1.66  tff(c_49, plain, (r1_tsep_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 4.09/1.66  tff(c_55, plain, (![D_52, B_53, C_54, A_55]: (r1_tsep_1(D_52, B_53) | ~r1_tsep_1(D_52, C_54) | ~m1_pre_topc(B_53, C_54) | ~m1_pre_topc(D_52, A_55) | v2_struct_0(D_52) | ~m1_pre_topc(C_54, A_55) | v2_struct_0(C_54) | ~m1_pre_topc(B_53, A_55) | v2_struct_0(B_53) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.09/1.66  tff(c_57, plain, (![B_53, A_55]: (r1_tsep_1('#skF_4', B_53) | ~m1_pre_topc(B_53, '#skF_2') | ~m1_pre_topc('#skF_4', A_55) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', A_55) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_53, A_55) | v2_struct_0(B_53) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(resolution, [status(thm)], [c_49, c_55])).
% 4.09/1.66  tff(c_61, plain, (![B_56, A_57]: (r1_tsep_1('#skF_4', B_56) | ~m1_pre_topc(B_56, '#skF_2') | ~m1_pre_topc('#skF_4', A_57) | ~m1_pre_topc('#skF_2', A_57) | ~m1_pre_topc(B_56, A_57) | v2_struct_0(B_56) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(negUnitSimplification, [status(thm)], [c_32, c_24, c_57])).
% 4.09/1.66  tff(c_63, plain, (![B_56]: (r1_tsep_1('#skF_4', B_56) | ~m1_pre_topc(B_56, '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_56, '#skF_1') | v2_struct_0(B_56) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_61])).
% 4.09/1.66  tff(c_66, plain, (![B_56]: (r1_tsep_1('#skF_4', B_56) | ~m1_pre_topc(B_56, '#skF_2') | ~m1_pre_topc(B_56, '#skF_1') | v2_struct_0(B_56) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_63])).
% 4.09/1.66  tff(c_68, plain, (![B_58]: (r1_tsep_1('#skF_4', B_58) | ~m1_pre_topc(B_58, '#skF_2') | ~m1_pre_topc(B_58, '#skF_1') | v2_struct_0(B_58))), inference(negUnitSimplification, [status(thm)], [c_38, c_66])).
% 4.09/1.66  tff(c_42, plain, (r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_2', '#skF_4') | ~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.09/1.66  tff(c_47, plain, (~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_42])).
% 4.09/1.66  tff(c_77, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_47])).
% 4.09/1.66  tff(c_89, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_77])).
% 4.09/1.66  tff(c_92, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_89])).
% 4.09/1.66  tff(c_95, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_92])).
% 4.09/1.66  tff(c_97, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_95])).
% 4.09/1.66  tff(c_98, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_77])).
% 4.09/1.66  tff(c_125, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_98])).
% 4.09/1.66  tff(c_128, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_125])).
% 4.09/1.66  tff(c_131, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_128])).
% 4.09/1.66  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_131])).
% 4.09/1.66  tff(c_134, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_98])).
% 4.09/1.66  tff(c_6, plain, (![A_1, B_2, C_3]: (~v2_struct_0(k2_tsep_1(A_1, B_2, C_3)) | ~m1_pre_topc(C_3, A_1) | v2_struct_0(C_3) | ~m1_pre_topc(B_2, A_1) | v2_struct_0(B_2) | ~l1_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.09/1.66  tff(c_138, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_134, c_6])).
% 4.09/1.66  tff(c_141, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_138])).
% 4.09/1.66  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_141])).
% 4.09/1.66  tff(c_144, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_46])).
% 4.09/1.66  tff(c_146, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_144])).
% 4.09/1.66  tff(c_207, plain, (![B_95, D_96, C_97, A_98]: (r1_tsep_1(B_95, D_96) | ~r1_tsep_1(C_97, D_96) | ~m1_pre_topc(B_95, C_97) | ~m1_pre_topc(D_96, A_98) | v2_struct_0(D_96) | ~m1_pre_topc(C_97, A_98) | v2_struct_0(C_97) | ~m1_pre_topc(B_95, A_98) | v2_struct_0(B_95) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.09/1.66  tff(c_213, plain, (![B_95, A_98]: (r1_tsep_1(B_95, '#skF_4') | ~m1_pre_topc(B_95, '#skF_3') | ~m1_pre_topc('#skF_4', A_98) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_98) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_95, A_98) | v2_struct_0(B_95) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(resolution, [status(thm)], [c_146, c_207])).
% 4.09/1.66  tff(c_223, plain, (![B_99, A_100]: (r1_tsep_1(B_99, '#skF_4') | ~m1_pre_topc(B_99, '#skF_3') | ~m1_pre_topc('#skF_4', A_100) | ~m1_pre_topc('#skF_3', A_100) | ~m1_pre_topc(B_99, A_100) | v2_struct_0(B_99) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(negUnitSimplification, [status(thm)], [c_28, c_24, c_213])).
% 4.09/1.66  tff(c_225, plain, (![B_99]: (r1_tsep_1(B_99, '#skF_4') | ~m1_pre_topc(B_99, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_99, '#skF_1') | v2_struct_0(B_99) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_223])).
% 4.09/1.66  tff(c_228, plain, (![B_99]: (r1_tsep_1(B_99, '#skF_4') | ~m1_pre_topc(B_99, '#skF_3') | ~m1_pre_topc(B_99, '#skF_1') | v2_struct_0(B_99) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_225])).
% 4.09/1.66  tff(c_230, plain, (![B_101]: (r1_tsep_1(B_101, '#skF_4') | ~m1_pre_topc(B_101, '#skF_3') | ~m1_pre_topc(B_101, '#skF_1') | v2_struct_0(B_101))), inference(negUnitSimplification, [status(thm)], [c_38, c_228])).
% 4.09/1.66  tff(c_44, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.09/1.66  tff(c_48, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 4.09/1.66  tff(c_249, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_230, c_48])).
% 4.09/1.66  tff(c_250, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_249])).
% 4.09/1.66  tff(c_253, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_250])).
% 4.09/1.66  tff(c_256, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_253])).
% 4.09/1.66  tff(c_258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_256])).
% 4.09/1.66  tff(c_259, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_249])).
% 4.09/1.66  tff(c_282, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_259])).
% 4.09/1.66  tff(c_285, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_282])).
% 4.09/1.66  tff(c_288, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_285])).
% 4.09/1.66  tff(c_290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_288])).
% 4.09/1.66  tff(c_291, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_259])).
% 4.09/1.66  tff(c_302, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_291, c_6])).
% 4.09/1.66  tff(c_305, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_302])).
% 4.09/1.66  tff(c_307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_305])).
% 4.09/1.66  tff(c_308, plain, (r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_144])).
% 4.09/1.66  tff(c_310, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_308])).
% 4.09/1.66  tff(c_316, plain, (![B_123, D_124, C_125, A_126]: (r1_tsep_1(B_123, D_124) | ~r1_tsep_1(D_124, C_125) | ~m1_pre_topc(B_123, C_125) | ~m1_pre_topc(D_124, A_126) | v2_struct_0(D_124) | ~m1_pre_topc(C_125, A_126) | v2_struct_0(C_125) | ~m1_pre_topc(B_123, A_126) | v2_struct_0(B_123) | ~l1_pre_topc(A_126) | ~v2_pre_topc(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.09/1.66  tff(c_318, plain, (![B_123, A_126]: (r1_tsep_1(B_123, '#skF_4') | ~m1_pre_topc(B_123, '#skF_3') | ~m1_pre_topc('#skF_4', A_126) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_126) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_123, A_126) | v2_struct_0(B_123) | ~l1_pre_topc(A_126) | ~v2_pre_topc(A_126) | v2_struct_0(A_126))), inference(resolution, [status(thm)], [c_310, c_316])).
% 4.09/1.66  tff(c_322, plain, (![B_127, A_128]: (r1_tsep_1(B_127, '#skF_4') | ~m1_pre_topc(B_127, '#skF_3') | ~m1_pre_topc('#skF_4', A_128) | ~m1_pre_topc('#skF_3', A_128) | ~m1_pre_topc(B_127, A_128) | v2_struct_0(B_127) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128) | v2_struct_0(A_128))), inference(negUnitSimplification, [status(thm)], [c_28, c_24, c_318])).
% 4.09/1.66  tff(c_324, plain, (![B_127]: (r1_tsep_1(B_127, '#skF_4') | ~m1_pre_topc(B_127, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_127, '#skF_1') | v2_struct_0(B_127) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_322])).
% 4.09/1.66  tff(c_327, plain, (![B_127]: (r1_tsep_1(B_127, '#skF_4') | ~m1_pre_topc(B_127, '#skF_3') | ~m1_pre_topc(B_127, '#skF_1') | v2_struct_0(B_127) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_324])).
% 4.09/1.67  tff(c_329, plain, (![B_129]: (r1_tsep_1(B_129, '#skF_4') | ~m1_pre_topc(B_129, '#skF_3') | ~m1_pre_topc(B_129, '#skF_1') | v2_struct_0(B_129))), inference(negUnitSimplification, [status(thm)], [c_38, c_327])).
% 4.09/1.67  tff(c_345, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_329, c_48])).
% 4.09/1.67  tff(c_346, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_345])).
% 4.09/1.67  tff(c_349, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_346])).
% 4.09/1.67  tff(c_352, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_349])).
% 4.09/1.67  tff(c_354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_352])).
% 4.09/1.67  tff(c_355, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_345])).
% 4.09/1.67  tff(c_368, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_355])).
% 4.09/1.67  tff(c_371, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_368])).
% 4.09/1.67  tff(c_374, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_371])).
% 4.09/1.67  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_374])).
% 4.09/1.67  tff(c_377, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_355])).
% 4.09/1.67  tff(c_388, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_377, c_6])).
% 4.09/1.67  tff(c_391, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_388])).
% 4.09/1.67  tff(c_393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_391])).
% 4.09/1.67  tff(c_394, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_308])).
% 4.09/1.67  tff(c_463, plain, (![B_165, D_166, C_167, A_168]: (r1_tsep_1(B_165, D_166) | ~r1_tsep_1(C_167, D_166) | ~m1_pre_topc(B_165, C_167) | ~m1_pre_topc(D_166, A_168) | v2_struct_0(D_166) | ~m1_pre_topc(C_167, A_168) | v2_struct_0(C_167) | ~m1_pre_topc(B_165, A_168) | v2_struct_0(B_165) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.09/1.67  tff(c_469, plain, (![B_165, A_168]: (r1_tsep_1(B_165, '#skF_4') | ~m1_pre_topc(B_165, '#skF_2') | ~m1_pre_topc('#skF_4', A_168) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', A_168) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_165, A_168) | v2_struct_0(B_165) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(resolution, [status(thm)], [c_394, c_463])).
% 4.09/1.67  tff(c_479, plain, (![B_169, A_170]: (r1_tsep_1(B_169, '#skF_4') | ~m1_pre_topc(B_169, '#skF_2') | ~m1_pre_topc('#skF_4', A_170) | ~m1_pre_topc('#skF_2', A_170) | ~m1_pre_topc(B_169, A_170) | v2_struct_0(B_169) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170))), inference(negUnitSimplification, [status(thm)], [c_32, c_24, c_469])).
% 4.09/1.67  tff(c_481, plain, (![B_169]: (r1_tsep_1(B_169, '#skF_4') | ~m1_pre_topc(B_169, '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_169, '#skF_1') | v2_struct_0(B_169) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_479])).
% 4.09/1.67  tff(c_484, plain, (![B_169]: (r1_tsep_1(B_169, '#skF_4') | ~m1_pre_topc(B_169, '#skF_2') | ~m1_pre_topc(B_169, '#skF_1') | v2_struct_0(B_169) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_481])).
% 4.09/1.67  tff(c_486, plain, (![B_171]: (r1_tsep_1(B_171, '#skF_4') | ~m1_pre_topc(B_171, '#skF_2') | ~m1_pre_topc(B_171, '#skF_1') | v2_struct_0(B_171))), inference(negUnitSimplification, [status(thm)], [c_38, c_484])).
% 4.09/1.67  tff(c_512, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_486, c_48])).
% 4.09/1.67  tff(c_513, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_512])).
% 4.09/1.67  tff(c_516, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_513])).
% 4.09/1.67  tff(c_519, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_516])).
% 4.09/1.67  tff(c_521, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_519])).
% 4.09/1.67  tff(c_522, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_512])).
% 4.09/1.67  tff(c_524, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_522])).
% 4.09/1.67  tff(c_527, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_524])).
% 4.09/1.67  tff(c_530, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_527])).
% 4.09/1.67  tff(c_532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_530])).
% 4.09/1.67  tff(c_533, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_522])).
% 4.09/1.67  tff(c_558, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_533, c_6])).
% 4.09/1.67  tff(c_561, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_558])).
% 4.09/1.67  tff(c_563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_561])).
% 4.09/1.67  tff(c_564, plain, (r1_tsep_1('#skF_4', '#skF_2') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 4.09/1.67  tff(c_566, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_564])).
% 4.09/1.67  tff(c_573, plain, (![D_191, B_192, C_193, A_194]: (r1_tsep_1(D_191, B_192) | ~r1_tsep_1(D_191, C_193) | ~m1_pre_topc(B_192, C_193) | ~m1_pre_topc(D_191, A_194) | v2_struct_0(D_191) | ~m1_pre_topc(C_193, A_194) | v2_struct_0(C_193) | ~m1_pre_topc(B_192, A_194) | v2_struct_0(B_192) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.09/1.67  tff(c_577, plain, (![B_192, A_194]: (r1_tsep_1('#skF_4', B_192) | ~m1_pre_topc(B_192, '#skF_3') | ~m1_pre_topc('#skF_4', A_194) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_194) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_192, A_194) | v2_struct_0(B_192) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194) | v2_struct_0(A_194))), inference(resolution, [status(thm)], [c_566, c_573])).
% 4.09/1.67  tff(c_584, plain, (![B_195, A_196]: (r1_tsep_1('#skF_4', B_195) | ~m1_pre_topc(B_195, '#skF_3') | ~m1_pre_topc('#skF_4', A_196) | ~m1_pre_topc('#skF_3', A_196) | ~m1_pre_topc(B_195, A_196) | v2_struct_0(B_195) | ~l1_pre_topc(A_196) | ~v2_pre_topc(A_196) | v2_struct_0(A_196))), inference(negUnitSimplification, [status(thm)], [c_28, c_24, c_577])).
% 4.09/1.67  tff(c_586, plain, (![B_195]: (r1_tsep_1('#skF_4', B_195) | ~m1_pre_topc(B_195, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_195, '#skF_1') | v2_struct_0(B_195) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_584])).
% 4.09/1.67  tff(c_589, plain, (![B_195]: (r1_tsep_1('#skF_4', B_195) | ~m1_pre_topc(B_195, '#skF_3') | ~m1_pre_topc(B_195, '#skF_1') | v2_struct_0(B_195) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_586])).
% 4.09/1.67  tff(c_591, plain, (![B_197]: (r1_tsep_1('#skF_4', B_197) | ~m1_pre_topc(B_197, '#skF_3') | ~m1_pre_topc(B_197, '#skF_1') | v2_struct_0(B_197))), inference(negUnitSimplification, [status(thm)], [c_38, c_589])).
% 4.09/1.67  tff(c_600, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_591, c_47])).
% 4.09/1.67  tff(c_601, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_600])).
% 4.09/1.67  tff(c_604, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_601])).
% 4.09/1.67  tff(c_607, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_604])).
% 4.09/1.67  tff(c_609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_607])).
% 4.09/1.67  tff(c_610, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_600])).
% 4.09/1.67  tff(c_612, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_610])).
% 4.09/1.67  tff(c_615, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_612])).
% 4.09/1.67  tff(c_618, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_615])).
% 4.09/1.67  tff(c_620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_618])).
% 4.09/1.67  tff(c_621, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_610])).
% 4.09/1.67  tff(c_641, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_621, c_6])).
% 4.09/1.67  tff(c_644, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_641])).
% 4.09/1.67  tff(c_646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_644])).
% 4.09/1.67  tff(c_647, plain, (r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_564])).
% 4.09/1.67  tff(c_656, plain, (![D_217, B_218, C_219, A_220]: (r1_tsep_1(D_217, B_218) | ~r1_tsep_1(D_217, C_219) | ~m1_pre_topc(B_218, C_219) | ~m1_pre_topc(D_217, A_220) | v2_struct_0(D_217) | ~m1_pre_topc(C_219, A_220) | v2_struct_0(C_219) | ~m1_pre_topc(B_218, A_220) | v2_struct_0(B_218) | ~l1_pre_topc(A_220) | ~v2_pre_topc(A_220) | v2_struct_0(A_220))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.09/1.67  tff(c_660, plain, (![B_218, A_220]: (r1_tsep_1('#skF_4', B_218) | ~m1_pre_topc(B_218, '#skF_2') | ~m1_pre_topc('#skF_4', A_220) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', A_220) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_218, A_220) | v2_struct_0(B_218) | ~l1_pre_topc(A_220) | ~v2_pre_topc(A_220) | v2_struct_0(A_220))), inference(resolution, [status(thm)], [c_647, c_656])).
% 4.09/1.67  tff(c_667, plain, (![B_221, A_222]: (r1_tsep_1('#skF_4', B_221) | ~m1_pre_topc(B_221, '#skF_2') | ~m1_pre_topc('#skF_4', A_222) | ~m1_pre_topc('#skF_2', A_222) | ~m1_pre_topc(B_221, A_222) | v2_struct_0(B_221) | ~l1_pre_topc(A_222) | ~v2_pre_topc(A_222) | v2_struct_0(A_222))), inference(negUnitSimplification, [status(thm)], [c_32, c_24, c_660])).
% 4.09/1.67  tff(c_669, plain, (![B_221]: (r1_tsep_1('#skF_4', B_221) | ~m1_pre_topc(B_221, '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_221, '#skF_1') | v2_struct_0(B_221) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_667])).
% 4.09/1.67  tff(c_672, plain, (![B_221]: (r1_tsep_1('#skF_4', B_221) | ~m1_pre_topc(B_221, '#skF_2') | ~m1_pre_topc(B_221, '#skF_1') | v2_struct_0(B_221) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_669])).
% 4.09/1.67  tff(c_674, plain, (![B_223]: (r1_tsep_1('#skF_4', B_223) | ~m1_pre_topc(B_223, '#skF_2') | ~m1_pre_topc(B_223, '#skF_1') | v2_struct_0(B_223))), inference(negUnitSimplification, [status(thm)], [c_38, c_672])).
% 4.09/1.67  tff(c_690, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_674, c_47])).
% 4.09/1.67  tff(c_691, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_690])).
% 4.09/1.67  tff(c_694, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_691])).
% 4.09/1.67  tff(c_697, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_694])).
% 4.09/1.67  tff(c_699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_697])).
% 4.09/1.67  tff(c_700, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_690])).
% 4.09/1.67  tff(c_702, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_700])).
% 4.09/1.67  tff(c_721, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_702])).
% 4.09/1.67  tff(c_724, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_721])).
% 4.09/1.67  tff(c_726, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_724])).
% 4.09/1.67  tff(c_727, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_700])).
% 4.09/1.67  tff(c_731, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_727, c_6])).
% 4.09/1.67  tff(c_734, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_731])).
% 4.09/1.67  tff(c_736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_734])).
% 4.09/1.67  tff(c_738, plain, (r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_42])).
% 4.09/1.67  tff(c_737, plain, (r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 4.09/1.67  tff(c_739, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_737])).
% 4.09/1.67  tff(c_861, plain, (![B_264, D_265, C_266, A_267]: (r1_tsep_1(B_264, D_265) | ~r1_tsep_1(C_266, D_265) | ~m1_pre_topc(B_264, C_266) | ~m1_pre_topc(D_265, A_267) | v2_struct_0(D_265) | ~m1_pre_topc(C_266, A_267) | v2_struct_0(C_266) | ~m1_pre_topc(B_264, A_267) | v2_struct_0(B_264) | ~l1_pre_topc(A_267) | ~v2_pre_topc(A_267) | v2_struct_0(A_267))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.09/1.67  tff(c_871, plain, (![B_264, A_267]: (r1_tsep_1(B_264, '#skF_4') | ~m1_pre_topc(B_264, '#skF_3') | ~m1_pre_topc('#skF_4', A_267) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_267) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_264, A_267) | v2_struct_0(B_264) | ~l1_pre_topc(A_267) | ~v2_pre_topc(A_267) | v2_struct_0(A_267))), inference(resolution, [status(thm)], [c_739, c_861])).
% 4.09/1.67  tff(c_887, plain, (![B_268, A_269]: (r1_tsep_1(B_268, '#skF_4') | ~m1_pre_topc(B_268, '#skF_3') | ~m1_pre_topc('#skF_4', A_269) | ~m1_pre_topc('#skF_3', A_269) | ~m1_pre_topc(B_268, A_269) | v2_struct_0(B_268) | ~l1_pre_topc(A_269) | ~v2_pre_topc(A_269) | v2_struct_0(A_269))), inference(negUnitSimplification, [status(thm)], [c_28, c_24, c_871])).
% 4.09/1.67  tff(c_889, plain, (![B_268]: (r1_tsep_1(B_268, '#skF_4') | ~m1_pre_topc(B_268, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_268, '#skF_1') | v2_struct_0(B_268) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_887])).
% 4.09/1.67  tff(c_892, plain, (![B_268]: (r1_tsep_1(B_268, '#skF_4') | ~m1_pre_topc(B_268, '#skF_3') | ~m1_pre_topc(B_268, '#skF_1') | v2_struct_0(B_268) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_889])).
% 4.09/1.67  tff(c_894, plain, (![B_270]: (r1_tsep_1(B_270, '#skF_4') | ~m1_pre_topc(B_270, '#skF_3') | ~m1_pre_topc(B_270, '#skF_1') | v2_struct_0(B_270))), inference(negUnitSimplification, [status(thm)], [c_38, c_892])).
% 4.09/1.67  tff(c_40, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.09/1.67  tff(c_740, plain, (~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_40])).
% 4.09/1.67  tff(c_742, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_738, c_740])).
% 4.09/1.67  tff(c_743, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 4.09/1.67  tff(c_918, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_894, c_743])).
% 4.09/1.67  tff(c_919, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_918])).
% 4.09/1.67  tff(c_922, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_919])).
% 4.09/1.67  tff(c_925, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_922])).
% 4.09/1.67  tff(c_927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_925])).
% 4.09/1.67  tff(c_928, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_918])).
% 4.09/1.67  tff(c_964, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_928])).
% 4.09/1.67  tff(c_967, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_964])).
% 4.09/1.67  tff(c_970, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_967])).
% 4.09/1.67  tff(c_972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_970])).
% 4.09/1.67  tff(c_973, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_928])).
% 4.09/1.67  tff(c_977, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_973, c_6])).
% 4.09/1.67  tff(c_980, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_977])).
% 4.09/1.67  tff(c_982, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_980])).
% 4.09/1.67  tff(c_983, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_737])).
% 4.09/1.67  tff(c_995, plain, (![B_289, D_290, C_291, A_292]: (r1_tsep_1(B_289, D_290) | ~r1_tsep_1(C_291, D_290) | ~m1_pre_topc(B_289, C_291) | ~m1_pre_topc(D_290, A_292) | v2_struct_0(D_290) | ~m1_pre_topc(C_291, A_292) | v2_struct_0(C_291) | ~m1_pre_topc(B_289, A_292) | v2_struct_0(B_289) | ~l1_pre_topc(A_292) | ~v2_pre_topc(A_292) | v2_struct_0(A_292))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.09/1.67  tff(c_999, plain, (![B_289, A_292]: (r1_tsep_1(B_289, '#skF_4') | ~m1_pre_topc(B_289, '#skF_2') | ~m1_pre_topc('#skF_4', A_292) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', A_292) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_289, A_292) | v2_struct_0(B_289) | ~l1_pre_topc(A_292) | ~v2_pre_topc(A_292) | v2_struct_0(A_292))), inference(resolution, [status(thm)], [c_983, c_995])).
% 4.09/1.67  tff(c_1006, plain, (![B_293, A_294]: (r1_tsep_1(B_293, '#skF_4') | ~m1_pre_topc(B_293, '#skF_2') | ~m1_pre_topc('#skF_4', A_294) | ~m1_pre_topc('#skF_2', A_294) | ~m1_pre_topc(B_293, A_294) | v2_struct_0(B_293) | ~l1_pre_topc(A_294) | ~v2_pre_topc(A_294) | v2_struct_0(A_294))), inference(negUnitSimplification, [status(thm)], [c_32, c_24, c_999])).
% 4.09/1.67  tff(c_1008, plain, (![B_293]: (r1_tsep_1(B_293, '#skF_4') | ~m1_pre_topc(B_293, '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_293, '#skF_1') | v2_struct_0(B_293) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_1006])).
% 4.09/1.67  tff(c_1011, plain, (![B_293]: (r1_tsep_1(B_293, '#skF_4') | ~m1_pre_topc(B_293, '#skF_2') | ~m1_pre_topc(B_293, '#skF_1') | v2_struct_0(B_293) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_1008])).
% 4.09/1.67  tff(c_1013, plain, (![B_295]: (r1_tsep_1(B_295, '#skF_4') | ~m1_pre_topc(B_295, '#skF_2') | ~m1_pre_topc(B_295, '#skF_1') | v2_struct_0(B_295))), inference(negUnitSimplification, [status(thm)], [c_38, c_1011])).
% 4.09/1.67  tff(c_985, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 4.09/1.67  tff(c_1025, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1013, c_985])).
% 4.09/1.67  tff(c_1030, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1025])).
% 4.09/1.67  tff(c_1033, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_1030])).
% 4.09/1.67  tff(c_1036, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_1033])).
% 4.09/1.67  tff(c_1038, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_1036])).
% 4.09/1.67  tff(c_1039, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1025])).
% 4.09/1.67  tff(c_1041, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1039])).
% 4.09/1.67  tff(c_1044, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1041])).
% 4.09/1.67  tff(c_1047, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_1044])).
% 4.09/1.67  tff(c_1049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_1047])).
% 4.09/1.67  tff(c_1050, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1039])).
% 4.09/1.67  tff(c_1070, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1050, c_6])).
% 4.09/1.67  tff(c_1073, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_1070])).
% 4.09/1.67  tff(c_1075, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_1073])).
% 4.09/1.67  tff(c_1077, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 4.09/1.67  tff(c_1082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_738, c_1077, c_40])).
% 4.09/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.67  
% 4.09/1.67  Inference rules
% 4.09/1.67  ----------------------
% 4.09/1.67  #Ref     : 0
% 4.09/1.67  #Sup     : 150
% 4.09/1.67  #Fact    : 0
% 4.09/1.67  #Define  : 0
% 4.09/1.67  #Split   : 26
% 4.09/1.67  #Chain   : 0
% 4.09/1.67  #Close   : 0
% 4.09/1.67  
% 4.09/1.67  Ordering : KBO
% 4.09/1.67  
% 4.09/1.67  Simplification rules
% 4.09/1.67  ----------------------
% 4.09/1.67  #Subsume      : 6
% 4.09/1.67  #Demod        : 169
% 4.09/1.67  #Tautology    : 6
% 4.09/1.67  #SimpNegUnit  : 142
% 4.09/1.67  #BackRed      : 0
% 4.09/1.67  
% 4.09/1.67  #Partial instantiations: 0
% 4.09/1.67  #Strategies tried      : 1
% 4.09/1.67  
% 4.09/1.67  Timing (in seconds)
% 4.09/1.67  ----------------------
% 4.09/1.67  Preprocessing        : 0.31
% 4.09/1.67  Parsing              : 0.17
% 4.09/1.67  CNF conversion       : 0.03
% 4.09/1.67  Main loop            : 0.55
% 4.09/1.67  Inferencing          : 0.20
% 4.09/1.67  Reduction            : 0.14
% 4.09/1.67  Demodulation         : 0.09
% 4.09/1.67  BG Simplification    : 0.03
% 4.09/1.67  Subsumption          : 0.15
% 4.09/1.67  Abstraction          : 0.02
% 4.09/1.67  MUC search           : 0.00
% 4.09/1.67  Cooper               : 0.00
% 4.09/1.67  Total                : 0.93
% 4.09/1.67  Index Insertion      : 0.00
% 4.09/1.67  Index Deletion       : 0.00
% 4.09/1.67  Index Matching       : 0.00
% 4.09/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
