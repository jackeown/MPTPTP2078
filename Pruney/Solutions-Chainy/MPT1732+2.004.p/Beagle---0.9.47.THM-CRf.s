%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:47 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :  229 (1232 expanded)
%              Number of leaves         :   18 ( 448 expanded)
%              Depth                    :   15
%              Number of atoms          :  940 (9264 expanded)
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
                   => ( ( ~ r1_tsep_1(C,D)
                        & ~ r1_tsep_1(D,C) )
                      | ( r1_tsep_1(B,D)
                        & r1_tsep_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tmap_1)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_20,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
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

tff(c_24,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_22,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
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
    ! [D_52,C_53,B_54,A_55] :
      ( ~ r1_tsep_1(D_52,C_53)
      | r1_tsep_1(D_52,B_54)
      | ~ m1_pre_topc(B_54,C_53)
      | ~ m1_pre_topc(D_52,A_55)
      | v2_struct_0(D_52)
      | ~ m1_pre_topc(C_53,A_55)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_54,A_55)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_57,plain,(
    ! [B_54,A_55] :
      ( r1_tsep_1('#skF_4',B_54)
      | ~ m1_pre_topc(B_54,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_55)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2',A_55)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_54,A_55)
      | v2_struct_0(B_54)
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

tff(c_124,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_127,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_124])).

tff(c_130,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_127])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_130])).

tff(c_133,plain,(
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

tff(c_137,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_133,c_6])).

tff(c_140,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_137])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_140])).

tff(c_143,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_145,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_164,plain,(
    ! [C_87,D_88,B_89,A_90] :
      ( ~ r1_tsep_1(C_87,D_88)
      | r1_tsep_1(B_89,D_88)
      | ~ m1_pre_topc(B_89,C_87)
      | ~ m1_pre_topc(D_88,A_90)
      | v2_struct_0(D_88)
      | ~ m1_pre_topc(C_87,A_90)
      | v2_struct_0(C_87)
      | ~ m1_pre_topc(B_89,A_90)
      | v2_struct_0(B_89)
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_166,plain,(
    ! [B_89,A_90] :
      ( r1_tsep_1(B_89,'#skF_4')
      | ~ m1_pre_topc(B_89,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_90)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_90)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_89,A_90)
      | v2_struct_0(B_89)
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_145,c_164])).

tff(c_181,plain,(
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
    inference(negUnitSimplification,[status(thm)],[c_28,c_24,c_166])).

tff(c_183,plain,(
    ! [B_92] :
      ( r1_tsep_1(B_92,'#skF_4')
      | ~ m1_pre_topc(B_92,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_92,'#skF_1')
      | v2_struct_0(B_92)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_181])).

tff(c_186,plain,(
    ! [B_92] :
      ( r1_tsep_1(B_92,'#skF_4')
      | ~ m1_pre_topc(B_92,'#skF_3')
      | ~ m1_pre_topc(B_92,'#skF_1')
      | v2_struct_0(B_92)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_183])).

tff(c_188,plain,(
    ! [B_94] :
      ( r1_tsep_1(B_94,'#skF_4')
      | ~ m1_pre_topc(B_94,'#skF_3')
      | ~ m1_pre_topc(B_94,'#skF_1')
      | v2_struct_0(B_94) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_186])).

tff(c_42,plain,
    ( ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_47,plain,(
    ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_202,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_188,c_47])).

tff(c_228,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_231,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_228])).

tff(c_234,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_231])).

tff(c_236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_234])).

tff(c_237,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_244,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_237])).

tff(c_247,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_244])).

tff(c_250,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_247])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_250])).

tff(c_253,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_273,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_253,c_6])).

tff(c_276,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_273])).

tff(c_278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_276])).

tff(c_279,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_281,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_313,plain,(
    ! [D_124,C_125,B_126,A_127] :
      ( ~ r1_tsep_1(D_124,C_125)
      | r1_tsep_1(B_126,D_124)
      | ~ m1_pre_topc(B_126,C_125)
      | ~ m1_pre_topc(D_124,A_127)
      | v2_struct_0(D_124)
      | ~ m1_pre_topc(C_125,A_127)
      | v2_struct_0(C_125)
      | ~ m1_pre_topc(B_126,A_127)
      | v2_struct_0(B_126)
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_317,plain,(
    ! [B_126,A_127] :
      ( r1_tsep_1(B_126,'#skF_4')
      | ~ m1_pre_topc(B_126,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_127)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_127)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_126,A_127)
      | v2_struct_0(B_126)
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_281,c_313])).

tff(c_324,plain,(
    ! [B_128,A_129] :
      ( r1_tsep_1(B_128,'#skF_4')
      | ~ m1_pre_topc(B_128,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_129)
      | ~ m1_pre_topc('#skF_3',A_129)
      | ~ m1_pre_topc(B_128,A_129)
      | v2_struct_0(B_128)
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_24,c_317])).

tff(c_326,plain,(
    ! [B_128] :
      ( r1_tsep_1(B_128,'#skF_4')
      | ~ m1_pre_topc(B_128,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_128,'#skF_1')
      | v2_struct_0(B_128)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_324])).

tff(c_329,plain,(
    ! [B_128] :
      ( r1_tsep_1(B_128,'#skF_4')
      | ~ m1_pre_topc(B_128,'#skF_3')
      | ~ m1_pre_topc(B_128,'#skF_1')
      | v2_struct_0(B_128)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_326])).

tff(c_331,plain,(
    ! [B_130] :
      ( r1_tsep_1(B_130,'#skF_4')
      | ~ m1_pre_topc(B_130,'#skF_3')
      | ~ m1_pre_topc(B_130,'#skF_1')
      | v2_struct_0(B_130) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_329])).

tff(c_352,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_331,c_47])).

tff(c_353,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_352])).

tff(c_372,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_353])).

tff(c_375,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_372])).

tff(c_377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_375])).

tff(c_378,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_380,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_417,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_380])).

tff(c_420,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_417])).

tff(c_422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_420])).

tff(c_423,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_427,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_423,c_6])).

tff(c_430,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_427])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_430])).

tff(c_433,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_440,plain,(
    ! [C_153,D_154,B_155,A_156] :
      ( ~ r1_tsep_1(C_153,D_154)
      | r1_tsep_1(B_155,D_154)
      | ~ m1_pre_topc(B_155,C_153)
      | ~ m1_pre_topc(D_154,A_156)
      | v2_struct_0(D_154)
      | ~ m1_pre_topc(C_153,A_156)
      | v2_struct_0(C_153)
      | ~ m1_pre_topc(B_155,A_156)
      | v2_struct_0(B_155)
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_442,plain,(
    ! [B_155,A_156] :
      ( r1_tsep_1(B_155,'#skF_4')
      | ~ m1_pre_topc(B_155,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_156)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2',A_156)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_155,A_156)
      | v2_struct_0(B_155)
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_433,c_440])).

tff(c_446,plain,(
    ! [B_157,A_158] :
      ( r1_tsep_1(B_157,'#skF_4')
      | ~ m1_pre_topc(B_157,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_158)
      | ~ m1_pre_topc('#skF_2',A_158)
      | ~ m1_pre_topc(B_157,A_158)
      | v2_struct_0(B_157)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_24,c_442])).

tff(c_448,plain,(
    ! [B_157] :
      ( r1_tsep_1(B_157,'#skF_4')
      | ~ m1_pre_topc(B_157,'#skF_2')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_157,'#skF_1')
      | v2_struct_0(B_157)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_446])).

tff(c_451,plain,(
    ! [B_157] :
      ( r1_tsep_1(B_157,'#skF_4')
      | ~ m1_pre_topc(B_157,'#skF_2')
      | ~ m1_pre_topc(B_157,'#skF_1')
      | v2_struct_0(B_157)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_448])).

tff(c_453,plain,(
    ! [B_159] :
      ( r1_tsep_1(B_159,'#skF_4')
      | ~ m1_pre_topc(B_159,'#skF_2')
      | ~ m1_pre_topc(B_159,'#skF_1')
      | v2_struct_0(B_159) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_451])).

tff(c_469,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_453,c_47])).

tff(c_470,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_469])).

tff(c_484,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_470])).

tff(c_487,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_484])).

tff(c_489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_487])).

tff(c_490,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_469])).

tff(c_492,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_490])).

tff(c_525,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_492])).

tff(c_528,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_525])).

tff(c_530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_528])).

tff(c_531,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_490])).

tff(c_535,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_531,c_6])).

tff(c_538,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_535])).

tff(c_540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_538])).

tff(c_542,plain,(
    r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_680,plain,(
    ! [D_214,C_215,B_216,A_217] :
      ( ~ r1_tsep_1(D_214,C_215)
      | r1_tsep_1(D_214,B_216)
      | ~ m1_pre_topc(B_216,C_215)
      | ~ m1_pre_topc(D_214,A_217)
      | v2_struct_0(D_214)
      | ~ m1_pre_topc(C_215,A_217)
      | v2_struct_0(C_215)
      | ~ m1_pre_topc(B_216,A_217)
      | v2_struct_0(B_216)
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_682,plain,(
    ! [B_216,A_217] :
      ( r1_tsep_1('#skF_4',B_216)
      | ~ m1_pre_topc(B_216,k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_4',A_217)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_217)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc(B_216,A_217)
      | v2_struct_0(B_216)
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_542,c_680])).

tff(c_687,plain,(
    ! [B_216,A_217] :
      ( r1_tsep_1('#skF_4',B_216)
      | ~ m1_pre_topc(B_216,k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_4',A_217)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_217)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc(B_216,A_217)
      | v2_struct_0(B_216)
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_682])).

tff(c_908,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_687])).

tff(c_911,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_908,c_6])).

tff(c_914,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_911])).

tff(c_916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_914])).

tff(c_918,plain,(
    ~ v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_687])).

tff(c_541,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_543,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_541])).

tff(c_576,plain,(
    ! [C_189,D_190,B_191,A_192] :
      ( ~ r1_tsep_1(C_189,D_190)
      | r1_tsep_1(B_191,D_190)
      | ~ m1_pre_topc(B_191,C_189)
      | ~ m1_pre_topc(D_190,A_192)
      | v2_struct_0(D_190)
      | ~ m1_pre_topc(C_189,A_192)
      | v2_struct_0(C_189)
      | ~ m1_pre_topc(B_191,A_192)
      | v2_struct_0(B_191)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_582,plain,(
    ! [B_191,A_192] :
      ( r1_tsep_1(B_191,'#skF_4')
      | ~ m1_pre_topc(B_191,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_192)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_192)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_191,A_192)
      | v2_struct_0(B_191)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(resolution,[status(thm)],[c_543,c_576])).

tff(c_592,plain,(
    ! [B_193,A_194] :
      ( r1_tsep_1(B_193,'#skF_4')
      | ~ m1_pre_topc(B_193,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_194)
      | ~ m1_pre_topc('#skF_3',A_194)
      | ~ m1_pre_topc(B_193,A_194)
      | v2_struct_0(B_193)
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_24,c_582])).

tff(c_594,plain,(
    ! [B_193] :
      ( r1_tsep_1(B_193,'#skF_4')
      | ~ m1_pre_topc(B_193,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_193,'#skF_1')
      | v2_struct_0(B_193)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_592])).

tff(c_597,plain,(
    ! [B_193] :
      ( r1_tsep_1(B_193,'#skF_4')
      | ~ m1_pre_topc(B_193,'#skF_3')
      | ~ m1_pre_topc(B_193,'#skF_1')
      | v2_struct_0(B_193)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_594])).

tff(c_599,plain,(
    ! [B_195] :
      ( r1_tsep_1(B_195,'#skF_4')
      | ~ m1_pre_topc(B_195,'#skF_3')
      | ~ m1_pre_topc(B_195,'#skF_1')
      | v2_struct_0(B_195) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_597])).

tff(c_613,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_599,c_47])).

tff(c_614,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_613])).

tff(c_642,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_614])).

tff(c_645,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_642])).

tff(c_647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_645])).

tff(c_648,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_613])).

tff(c_650,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_648])).

tff(c_653,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_650])).

tff(c_656,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_653])).

tff(c_658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_656])).

tff(c_659,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_648])).

tff(c_663,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_659,c_6])).

tff(c_666,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_663])).

tff(c_668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_666])).

tff(c_669,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_541])).

tff(c_843,plain,(
    ! [C_241,D_242,B_243,A_244] :
      ( ~ r1_tsep_1(C_241,D_242)
      | r1_tsep_1(B_243,D_242)
      | ~ m1_pre_topc(B_243,C_241)
      | ~ m1_pre_topc(D_242,A_244)
      | v2_struct_0(D_242)
      | ~ m1_pre_topc(C_241,A_244)
      | v2_struct_0(C_241)
      | ~ m1_pre_topc(B_243,A_244)
      | v2_struct_0(B_243)
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_853,plain,(
    ! [B_243,A_244] :
      ( r1_tsep_1(B_243,'#skF_4')
      | ~ m1_pre_topc(B_243,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_244)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2',A_244)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_243,A_244)
      | v2_struct_0(B_243)
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244) ) ),
    inference(resolution,[status(thm)],[c_669,c_843])).

tff(c_869,plain,(
    ! [B_245,A_246] :
      ( r1_tsep_1(B_245,'#skF_4')
      | ~ m1_pre_topc(B_245,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_246)
      | ~ m1_pre_topc('#skF_2',A_246)
      | ~ m1_pre_topc(B_245,A_246)
      | v2_struct_0(B_245)
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_24,c_853])).

tff(c_871,plain,(
    ! [B_245] :
      ( r1_tsep_1(B_245,'#skF_4')
      | ~ m1_pre_topc(B_245,'#skF_2')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_245,'#skF_1')
      | v2_struct_0(B_245)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_869])).

tff(c_874,plain,(
    ! [B_245] :
      ( r1_tsep_1(B_245,'#skF_4')
      | ~ m1_pre_topc(B_245,'#skF_2')
      | ~ m1_pre_topc(B_245,'#skF_1')
      | v2_struct_0(B_245)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_871])).

tff(c_876,plain,(
    ! [B_247] :
      ( r1_tsep_1(B_247,'#skF_4')
      | ~ m1_pre_topc(B_247,'#skF_2')
      | ~ m1_pre_topc(B_247,'#skF_1')
      | v2_struct_0(B_247) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_874])).

tff(c_907,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_876,c_47])).

tff(c_941,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_918,c_907])).

tff(c_942,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_941])).

tff(c_945,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_942])).

tff(c_948,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_945])).

tff(c_950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_948])).

tff(c_951,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_941])).

tff(c_969,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_951])).

tff(c_972,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_969])).

tff(c_974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_972])).

tff(c_976,plain,(
    r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1224,plain,(
    ! [C_316,D_317,B_318,A_319] :
      ( ~ r1_tsep_1(C_316,D_317)
      | r1_tsep_1(D_317,B_318)
      | ~ m1_pre_topc(B_318,C_316)
      | ~ m1_pre_topc(D_317,A_319)
      | v2_struct_0(D_317)
      | ~ m1_pre_topc(C_316,A_319)
      | v2_struct_0(C_316)
      | ~ m1_pre_topc(B_318,A_319)
      | v2_struct_0(B_318)
      | ~ l1_pre_topc(A_319)
      | ~ v2_pre_topc(A_319)
      | v2_struct_0(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1228,plain,(
    ! [B_318,A_319] :
      ( r1_tsep_1('#skF_4',B_318)
      | ~ m1_pre_topc(B_318,k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_4',A_319)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_319)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc(B_318,A_319)
      | v2_struct_0(B_318)
      | ~ l1_pre_topc(A_319)
      | ~ v2_pre_topc(A_319)
      | v2_struct_0(A_319) ) ),
    inference(resolution,[status(thm)],[c_976,c_1224])).

tff(c_1236,plain,(
    ! [B_318,A_319] :
      ( r1_tsep_1('#skF_4',B_318)
      | ~ m1_pre_topc(B_318,k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_4',A_319)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_319)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc(B_318,A_319)
      | v2_struct_0(B_318)
      | ~ l1_pre_topc(A_319)
      | ~ v2_pre_topc(A_319)
      | v2_struct_0(A_319) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1228])).

tff(c_1374,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1236])).

tff(c_1377,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1374,c_6])).

tff(c_1380,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_1377])).

tff(c_1382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_1380])).

tff(c_1384,plain,(
    ~ v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1236])).

tff(c_1045,plain,(
    ! [D_280,C_281,B_282,A_283] :
      ( ~ r1_tsep_1(D_280,C_281)
      | r1_tsep_1(D_280,B_282)
      | ~ m1_pre_topc(B_282,C_281)
      | ~ m1_pre_topc(D_280,A_283)
      | v2_struct_0(D_280)
      | ~ m1_pre_topc(C_281,A_283)
      | v2_struct_0(C_281)
      | ~ m1_pre_topc(B_282,A_283)
      | v2_struct_0(B_282)
      | ~ l1_pre_topc(A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1051,plain,(
    ! [B_282,A_283] :
      ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),B_282)
      | ~ m1_pre_topc(B_282,'#skF_4')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_283)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_4',A_283)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_282,A_283)
      | v2_struct_0(B_282)
      | ~ l1_pre_topc(A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283) ) ),
    inference(resolution,[status(thm)],[c_976,c_1045])).

tff(c_1062,plain,(
    ! [B_282,A_283] :
      ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),B_282)
      | ~ m1_pre_topc(B_282,'#skF_4')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_283)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_4',A_283)
      | ~ m1_pre_topc(B_282,A_283)
      | v2_struct_0(B_282)
      | ~ l1_pre_topc(A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1051])).

tff(c_1176,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1062])).

tff(c_1179,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1176,c_6])).

tff(c_1182,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_1179])).

tff(c_1184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_1182])).

tff(c_1186,plain,(
    ~ v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1062])).

tff(c_975,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_977,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_975])).

tff(c_1053,plain,(
    ! [B_282,A_283] :
      ( r1_tsep_1('#skF_4',B_282)
      | ~ m1_pre_topc(B_282,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_283)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_283)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_282,A_283)
      | v2_struct_0(B_282)
      | ~ l1_pre_topc(A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283) ) ),
    inference(resolution,[status(thm)],[c_977,c_1045])).

tff(c_1066,plain,(
    ! [B_284,A_285] :
      ( r1_tsep_1('#skF_4',B_284)
      | ~ m1_pre_topc(B_284,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_285)
      | ~ m1_pre_topc('#skF_3',A_285)
      | ~ m1_pre_topc(B_284,A_285)
      | v2_struct_0(B_284)
      | ~ l1_pre_topc(A_285)
      | ~ v2_pre_topc(A_285)
      | v2_struct_0(A_285) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_24,c_1053])).

tff(c_1068,plain,(
    ! [B_284] :
      ( r1_tsep_1('#skF_4',B_284)
      | ~ m1_pre_topc(B_284,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_284,'#skF_1')
      | v2_struct_0(B_284)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_1066])).

tff(c_1071,plain,(
    ! [B_284] :
      ( r1_tsep_1('#skF_4',B_284)
      | ~ m1_pre_topc(B_284,'#skF_3')
      | ~ m1_pre_topc(B_284,'#skF_1')
      | v2_struct_0(B_284)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_1068])).

tff(c_1094,plain,(
    ! [B_290] :
      ( r1_tsep_1('#skF_4',B_290)
      | ~ m1_pre_topc(B_290,'#skF_3')
      | ~ m1_pre_topc(B_290,'#skF_1')
      | v2_struct_0(B_290) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1071])).

tff(c_46,plain,
    ( ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_980,plain,(
    ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_976,c_46])).

tff(c_1118,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1094,c_980])).

tff(c_1119,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1118])).

tff(c_1122,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_1119])).

tff(c_1125,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_1122])).

tff(c_1127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_1125])).

tff(c_1128,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1118])).

tff(c_1165,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1128])).

tff(c_1168,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_1165])).

tff(c_1171,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_1168])).

tff(c_1173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_1171])).

tff(c_1174,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1128])).

tff(c_1187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1186,c_1174])).

tff(c_1188,plain,(
    r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_975])).

tff(c_1309,plain,(
    ! [D_330,C_331,B_332,A_333] :
      ( ~ r1_tsep_1(D_330,C_331)
      | r1_tsep_1(D_330,B_332)
      | ~ m1_pre_topc(B_332,C_331)
      | ~ m1_pre_topc(D_330,A_333)
      | v2_struct_0(D_330)
      | ~ m1_pre_topc(C_331,A_333)
      | v2_struct_0(C_331)
      | ~ m1_pre_topc(B_332,A_333)
      | v2_struct_0(B_332)
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333)
      | v2_struct_0(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1319,plain,(
    ! [B_332,A_333] :
      ( r1_tsep_1('#skF_4',B_332)
      | ~ m1_pre_topc(B_332,'#skF_2')
      | ~ m1_pre_topc('#skF_4',A_333)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2',A_333)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_332,A_333)
      | v2_struct_0(B_332)
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333)
      | v2_struct_0(A_333) ) ),
    inference(resolution,[status(thm)],[c_1188,c_1309])).

tff(c_1335,plain,(
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
    inference(negUnitSimplification,[status(thm)],[c_32,c_24,c_1319])).

tff(c_1337,plain,(
    ! [B_334] :
      ( r1_tsep_1('#skF_4',B_334)
      | ~ m1_pre_topc(B_334,'#skF_2')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_334,'#skF_1')
      | v2_struct_0(B_334)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_1335])).

tff(c_1340,plain,(
    ! [B_334] :
      ( r1_tsep_1('#skF_4',B_334)
      | ~ m1_pre_topc(B_334,'#skF_2')
      | ~ m1_pre_topc(B_334,'#skF_1')
      | v2_struct_0(B_334)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_22,c_1337])).

tff(c_1342,plain,(
    ! [B_336] :
      ( r1_tsep_1('#skF_4',B_336)
      | ~ m1_pre_topc(B_336,'#skF_2')
      | ~ m1_pre_topc(B_336,'#skF_1')
      | v2_struct_0(B_336) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1340])).

tff(c_1190,plain,(
    ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_1369,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1342,c_1190])).

tff(c_1385,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1384,c_1369])).

tff(c_1386,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1385])).

tff(c_1414,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_1386])).

tff(c_1417,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_26,c_1414])).

tff(c_1419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_1417])).

tff(c_1420,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1385])).

tff(c_1424,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1420])).

tff(c_1427,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_26,c_1424])).

tff(c_1429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_28,c_20,c_1427])).

tff(c_1431,plain,(
    r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1431,c_976,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:27:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.55/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.80  
% 4.55/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.80  %$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.55/1.80  
% 4.55/1.80  %Foreground sorts:
% 4.55/1.80  
% 4.55/1.80  
% 4.55/1.80  %Background operators:
% 4.55/1.80  
% 4.55/1.80  
% 4.55/1.80  %Foreground operators:
% 4.55/1.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.55/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.55/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.55/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.55/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.55/1.80  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.55/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.55/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.80  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.55/1.80  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 4.55/1.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.55/1.80  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 4.55/1.81  
% 4.83/1.86  tff(f_157, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(B, C) => ((~r1_tsep_1(k2_tsep_1(A, B, C), D) => (~r1_tsep_1(B, D) & ~r1_tsep_1(C, D))) & (~r1_tsep_1(D, k2_tsep_1(A, B, C)) => (~r1_tsep_1(D, B) & ~r1_tsep_1(D, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tmap_1)).
% 4.83/1.86  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (m1_pre_topc(k2_tsep_1(A, B, C), B) & m1_pre_topc(k2_tsep_1(A, B, C), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tsep_1)).
% 4.83/1.86  tff(f_47, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 4.83/1.86  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)) | (r1_tsep_1(B, D) & r1_tsep_1(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tmap_1)).
% 4.83/1.86  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.83/1.86  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.83/1.86  tff(c_28, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.83/1.86  tff(c_20, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.83/1.86  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.83/1.86  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.83/1.86  tff(c_30, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.83/1.86  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.83/1.86  tff(c_18, plain, (![A_19, B_23, C_25]: (m1_pre_topc(k2_tsep_1(A_19, B_23, C_25), B_23) | r1_tsep_1(B_23, C_25) | ~m1_pre_topc(C_25, A_19) | v2_struct_0(C_25) | ~m1_pre_topc(B_23, A_19) | v2_struct_0(B_23) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.83/1.86  tff(c_2, plain, (![A_1, B_2, C_3]: (m1_pre_topc(k2_tsep_1(A_1, B_2, C_3), A_1) | ~m1_pre_topc(C_3, A_1) | v2_struct_0(C_3) | ~m1_pre_topc(B_2, A_1) | v2_struct_0(B_2) | ~l1_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.83/1.86  tff(c_24, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.83/1.86  tff(c_22, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.83/1.86  tff(c_16, plain, (![A_19, B_23, C_25]: (m1_pre_topc(k2_tsep_1(A_19, B_23, C_25), C_25) | r1_tsep_1(B_23, C_25) | ~m1_pre_topc(C_25, A_19) | v2_struct_0(C_25) | ~m1_pre_topc(B_23, A_19) | v2_struct_0(B_23) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.83/1.86  tff(c_40, plain, (r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.83/1.86  tff(c_49, plain, (r1_tsep_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 4.83/1.86  tff(c_55, plain, (![D_52, C_53, B_54, A_55]: (~r1_tsep_1(D_52, C_53) | r1_tsep_1(D_52, B_54) | ~m1_pre_topc(B_54, C_53) | ~m1_pre_topc(D_52, A_55) | v2_struct_0(D_52) | ~m1_pre_topc(C_53, A_55) | v2_struct_0(C_53) | ~m1_pre_topc(B_54, A_55) | v2_struct_0(B_54) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.83/1.86  tff(c_57, plain, (![B_54, A_55]: (r1_tsep_1('#skF_4', B_54) | ~m1_pre_topc(B_54, '#skF_2') | ~m1_pre_topc('#skF_4', A_55) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', A_55) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_54, A_55) | v2_struct_0(B_54) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(resolution, [status(thm)], [c_49, c_55])).
% 4.83/1.86  tff(c_61, plain, (![B_56, A_57]: (r1_tsep_1('#skF_4', B_56) | ~m1_pre_topc(B_56, '#skF_2') | ~m1_pre_topc('#skF_4', A_57) | ~m1_pre_topc('#skF_2', A_57) | ~m1_pre_topc(B_56, A_57) | v2_struct_0(B_56) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(negUnitSimplification, [status(thm)], [c_32, c_24, c_57])).
% 4.83/1.86  tff(c_63, plain, (![B_56]: (r1_tsep_1('#skF_4', B_56) | ~m1_pre_topc(B_56, '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_56, '#skF_1') | v2_struct_0(B_56) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_61])).
% 4.83/1.86  tff(c_66, plain, (![B_56]: (r1_tsep_1('#skF_4', B_56) | ~m1_pre_topc(B_56, '#skF_2') | ~m1_pre_topc(B_56, '#skF_1') | v2_struct_0(B_56) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_63])).
% 4.83/1.86  tff(c_68, plain, (![B_58]: (r1_tsep_1('#skF_4', B_58) | ~m1_pre_topc(B_58, '#skF_2') | ~m1_pre_topc(B_58, '#skF_1') | v2_struct_0(B_58))), inference(negUnitSimplification, [status(thm)], [c_38, c_66])).
% 4.83/1.86  tff(c_44, plain, (r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_2', '#skF_4') | ~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.83/1.86  tff(c_48, plain, (~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_44])).
% 4.83/1.86  tff(c_77, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_48])).
% 4.83/1.86  tff(c_89, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_77])).
% 4.83/1.86  tff(c_92, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_89])).
% 4.83/1.86  tff(c_95, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_92])).
% 4.83/1.86  tff(c_97, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_95])).
% 4.83/1.86  tff(c_98, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_77])).
% 4.83/1.86  tff(c_124, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_98])).
% 4.83/1.86  tff(c_127, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_124])).
% 4.83/1.86  tff(c_130, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_127])).
% 4.83/1.86  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_130])).
% 4.83/1.86  tff(c_133, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_98])).
% 4.83/1.86  tff(c_6, plain, (![A_1, B_2, C_3]: (~v2_struct_0(k2_tsep_1(A_1, B_2, C_3)) | ~m1_pre_topc(C_3, A_1) | v2_struct_0(C_3) | ~m1_pre_topc(B_2, A_1) | v2_struct_0(B_2) | ~l1_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.83/1.86  tff(c_137, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_133, c_6])).
% 4.83/1.86  tff(c_140, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_137])).
% 4.83/1.86  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_140])).
% 4.83/1.86  tff(c_143, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 4.83/1.86  tff(c_145, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_143])).
% 4.83/1.86  tff(c_164, plain, (![C_87, D_88, B_89, A_90]: (~r1_tsep_1(C_87, D_88) | r1_tsep_1(B_89, D_88) | ~m1_pre_topc(B_89, C_87) | ~m1_pre_topc(D_88, A_90) | v2_struct_0(D_88) | ~m1_pre_topc(C_87, A_90) | v2_struct_0(C_87) | ~m1_pre_topc(B_89, A_90) | v2_struct_0(B_89) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.83/1.86  tff(c_166, plain, (![B_89, A_90]: (r1_tsep_1(B_89, '#skF_4') | ~m1_pre_topc(B_89, '#skF_3') | ~m1_pre_topc('#skF_4', A_90) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_90) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_89, A_90) | v2_struct_0(B_89) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90) | v2_struct_0(A_90))), inference(resolution, [status(thm)], [c_145, c_164])).
% 4.83/1.86  tff(c_181, plain, (![B_92, A_93]: (r1_tsep_1(B_92, '#skF_4') | ~m1_pre_topc(B_92, '#skF_3') | ~m1_pre_topc('#skF_4', A_93) | ~m1_pre_topc('#skF_3', A_93) | ~m1_pre_topc(B_92, A_93) | v2_struct_0(B_92) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(negUnitSimplification, [status(thm)], [c_28, c_24, c_166])).
% 4.83/1.86  tff(c_183, plain, (![B_92]: (r1_tsep_1(B_92, '#skF_4') | ~m1_pre_topc(B_92, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_92, '#skF_1') | v2_struct_0(B_92) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_181])).
% 4.83/1.86  tff(c_186, plain, (![B_92]: (r1_tsep_1(B_92, '#skF_4') | ~m1_pre_topc(B_92, '#skF_3') | ~m1_pre_topc(B_92, '#skF_1') | v2_struct_0(B_92) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_183])).
% 4.83/1.86  tff(c_188, plain, (![B_94]: (r1_tsep_1(B_94, '#skF_4') | ~m1_pre_topc(B_94, '#skF_3') | ~m1_pre_topc(B_94, '#skF_1') | v2_struct_0(B_94))), inference(negUnitSimplification, [status(thm)], [c_38, c_186])).
% 4.83/1.86  tff(c_42, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.83/1.86  tff(c_47, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_42])).
% 4.83/1.86  tff(c_202, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_188, c_47])).
% 4.83/1.86  tff(c_228, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_202])).
% 4.83/1.86  tff(c_231, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_228])).
% 4.83/1.86  tff(c_234, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_231])).
% 4.83/1.86  tff(c_236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_234])).
% 4.83/1.86  tff(c_237, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_202])).
% 4.83/1.86  tff(c_244, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_237])).
% 4.83/1.86  tff(c_247, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_244])).
% 4.83/1.86  tff(c_250, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_247])).
% 4.83/1.86  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_250])).
% 4.83/1.86  tff(c_253, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_237])).
% 4.83/1.86  tff(c_273, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_253, c_6])).
% 4.83/1.86  tff(c_276, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_273])).
% 4.83/1.86  tff(c_278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_276])).
% 4.83/1.86  tff(c_279, plain, (r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_143])).
% 4.83/1.86  tff(c_281, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_279])).
% 4.83/1.86  tff(c_313, plain, (![D_124, C_125, B_126, A_127]: (~r1_tsep_1(D_124, C_125) | r1_tsep_1(B_126, D_124) | ~m1_pre_topc(B_126, C_125) | ~m1_pre_topc(D_124, A_127) | v2_struct_0(D_124) | ~m1_pre_topc(C_125, A_127) | v2_struct_0(C_125) | ~m1_pre_topc(B_126, A_127) | v2_struct_0(B_126) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.83/1.86  tff(c_317, plain, (![B_126, A_127]: (r1_tsep_1(B_126, '#skF_4') | ~m1_pre_topc(B_126, '#skF_3') | ~m1_pre_topc('#skF_4', A_127) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_127) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_126, A_127) | v2_struct_0(B_126) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127) | v2_struct_0(A_127))), inference(resolution, [status(thm)], [c_281, c_313])).
% 4.83/1.86  tff(c_324, plain, (![B_128, A_129]: (r1_tsep_1(B_128, '#skF_4') | ~m1_pre_topc(B_128, '#skF_3') | ~m1_pre_topc('#skF_4', A_129) | ~m1_pre_topc('#skF_3', A_129) | ~m1_pre_topc(B_128, A_129) | v2_struct_0(B_128) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129))), inference(negUnitSimplification, [status(thm)], [c_28, c_24, c_317])).
% 4.83/1.86  tff(c_326, plain, (![B_128]: (r1_tsep_1(B_128, '#skF_4') | ~m1_pre_topc(B_128, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_128, '#skF_1') | v2_struct_0(B_128) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_324])).
% 4.83/1.86  tff(c_329, plain, (![B_128]: (r1_tsep_1(B_128, '#skF_4') | ~m1_pre_topc(B_128, '#skF_3') | ~m1_pre_topc(B_128, '#skF_1') | v2_struct_0(B_128) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_326])).
% 4.83/1.86  tff(c_331, plain, (![B_130]: (r1_tsep_1(B_130, '#skF_4') | ~m1_pre_topc(B_130, '#skF_3') | ~m1_pre_topc(B_130, '#skF_1') | v2_struct_0(B_130))), inference(negUnitSimplification, [status(thm)], [c_38, c_329])).
% 4.83/1.86  tff(c_352, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_331, c_47])).
% 4.83/1.86  tff(c_353, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_352])).
% 4.83/1.86  tff(c_372, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_353])).
% 4.83/1.86  tff(c_375, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_372])).
% 4.83/1.86  tff(c_377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_375])).
% 4.83/1.86  tff(c_378, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_352])).
% 4.83/1.86  tff(c_380, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_378])).
% 4.83/1.86  tff(c_417, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_380])).
% 4.83/1.86  tff(c_420, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_417])).
% 4.83/1.86  tff(c_422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_420])).
% 4.83/1.86  tff(c_423, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_378])).
% 4.83/1.86  tff(c_427, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_423, c_6])).
% 4.83/1.86  tff(c_430, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_427])).
% 4.83/1.86  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_430])).
% 4.83/1.86  tff(c_433, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_279])).
% 4.83/1.86  tff(c_440, plain, (![C_153, D_154, B_155, A_156]: (~r1_tsep_1(C_153, D_154) | r1_tsep_1(B_155, D_154) | ~m1_pre_topc(B_155, C_153) | ~m1_pre_topc(D_154, A_156) | v2_struct_0(D_154) | ~m1_pre_topc(C_153, A_156) | v2_struct_0(C_153) | ~m1_pre_topc(B_155, A_156) | v2_struct_0(B_155) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.83/1.86  tff(c_442, plain, (![B_155, A_156]: (r1_tsep_1(B_155, '#skF_4') | ~m1_pre_topc(B_155, '#skF_2') | ~m1_pre_topc('#skF_4', A_156) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', A_156) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_155, A_156) | v2_struct_0(B_155) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156))), inference(resolution, [status(thm)], [c_433, c_440])).
% 4.83/1.86  tff(c_446, plain, (![B_157, A_158]: (r1_tsep_1(B_157, '#skF_4') | ~m1_pre_topc(B_157, '#skF_2') | ~m1_pre_topc('#skF_4', A_158) | ~m1_pre_topc('#skF_2', A_158) | ~m1_pre_topc(B_157, A_158) | v2_struct_0(B_157) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(negUnitSimplification, [status(thm)], [c_32, c_24, c_442])).
% 4.83/1.86  tff(c_448, plain, (![B_157]: (r1_tsep_1(B_157, '#skF_4') | ~m1_pre_topc(B_157, '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_157, '#skF_1') | v2_struct_0(B_157) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_446])).
% 4.83/1.86  tff(c_451, plain, (![B_157]: (r1_tsep_1(B_157, '#skF_4') | ~m1_pre_topc(B_157, '#skF_2') | ~m1_pre_topc(B_157, '#skF_1') | v2_struct_0(B_157) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_448])).
% 4.83/1.86  tff(c_453, plain, (![B_159]: (r1_tsep_1(B_159, '#skF_4') | ~m1_pre_topc(B_159, '#skF_2') | ~m1_pre_topc(B_159, '#skF_1') | v2_struct_0(B_159))), inference(negUnitSimplification, [status(thm)], [c_38, c_451])).
% 4.83/1.86  tff(c_469, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_453, c_47])).
% 4.83/1.86  tff(c_470, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_469])).
% 4.83/1.86  tff(c_484, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_470])).
% 4.83/1.86  tff(c_487, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_484])).
% 4.83/1.86  tff(c_489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_487])).
% 4.83/1.86  tff(c_490, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_469])).
% 4.83/1.86  tff(c_492, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_490])).
% 4.83/1.86  tff(c_525, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_492])).
% 4.83/1.86  tff(c_528, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_525])).
% 4.83/1.86  tff(c_530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_528])).
% 4.83/1.86  tff(c_531, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_490])).
% 4.83/1.86  tff(c_535, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_531, c_6])).
% 4.83/1.86  tff(c_538, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_535])).
% 4.83/1.86  tff(c_540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_538])).
% 4.83/1.86  tff(c_542, plain, (r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_44])).
% 4.83/1.86  tff(c_680, plain, (![D_214, C_215, B_216, A_217]: (~r1_tsep_1(D_214, C_215) | r1_tsep_1(D_214, B_216) | ~m1_pre_topc(B_216, C_215) | ~m1_pre_topc(D_214, A_217) | v2_struct_0(D_214) | ~m1_pre_topc(C_215, A_217) | v2_struct_0(C_215) | ~m1_pre_topc(B_216, A_217) | v2_struct_0(B_216) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217) | v2_struct_0(A_217))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.83/1.86  tff(c_682, plain, (![B_216, A_217]: (r1_tsep_1('#skF_4', B_216) | ~m1_pre_topc(B_216, k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_4', A_217) | v2_struct_0('#skF_4') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_217) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc(B_216, A_217) | v2_struct_0(B_216) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217) | v2_struct_0(A_217))), inference(resolution, [status(thm)], [c_542, c_680])).
% 4.83/1.86  tff(c_687, plain, (![B_216, A_217]: (r1_tsep_1('#skF_4', B_216) | ~m1_pre_topc(B_216, k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_4', A_217) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_217) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc(B_216, A_217) | v2_struct_0(B_216) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217) | v2_struct_0(A_217))), inference(negUnitSimplification, [status(thm)], [c_24, c_682])).
% 4.83/1.86  tff(c_908, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_687])).
% 4.83/1.86  tff(c_911, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_908, c_6])).
% 4.83/1.86  tff(c_914, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_911])).
% 4.83/1.86  tff(c_916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_914])).
% 4.83/1.86  tff(c_918, plain, (~v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_687])).
% 4.83/1.86  tff(c_541, plain, (r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 4.83/1.86  tff(c_543, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_541])).
% 4.83/1.86  tff(c_576, plain, (![C_189, D_190, B_191, A_192]: (~r1_tsep_1(C_189, D_190) | r1_tsep_1(B_191, D_190) | ~m1_pre_topc(B_191, C_189) | ~m1_pre_topc(D_190, A_192) | v2_struct_0(D_190) | ~m1_pre_topc(C_189, A_192) | v2_struct_0(C_189) | ~m1_pre_topc(B_191, A_192) | v2_struct_0(B_191) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.83/1.86  tff(c_582, plain, (![B_191, A_192]: (r1_tsep_1(B_191, '#skF_4') | ~m1_pre_topc(B_191, '#skF_3') | ~m1_pre_topc('#skF_4', A_192) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_192) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_191, A_192) | v2_struct_0(B_191) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192))), inference(resolution, [status(thm)], [c_543, c_576])).
% 4.83/1.86  tff(c_592, plain, (![B_193, A_194]: (r1_tsep_1(B_193, '#skF_4') | ~m1_pre_topc(B_193, '#skF_3') | ~m1_pre_topc('#skF_4', A_194) | ~m1_pre_topc('#skF_3', A_194) | ~m1_pre_topc(B_193, A_194) | v2_struct_0(B_193) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194) | v2_struct_0(A_194))), inference(negUnitSimplification, [status(thm)], [c_28, c_24, c_582])).
% 4.83/1.86  tff(c_594, plain, (![B_193]: (r1_tsep_1(B_193, '#skF_4') | ~m1_pre_topc(B_193, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_193, '#skF_1') | v2_struct_0(B_193) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_592])).
% 4.83/1.86  tff(c_597, plain, (![B_193]: (r1_tsep_1(B_193, '#skF_4') | ~m1_pre_topc(B_193, '#skF_3') | ~m1_pre_topc(B_193, '#skF_1') | v2_struct_0(B_193) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_594])).
% 4.83/1.86  tff(c_599, plain, (![B_195]: (r1_tsep_1(B_195, '#skF_4') | ~m1_pre_topc(B_195, '#skF_3') | ~m1_pre_topc(B_195, '#skF_1') | v2_struct_0(B_195))), inference(negUnitSimplification, [status(thm)], [c_38, c_597])).
% 4.83/1.86  tff(c_613, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_599, c_47])).
% 4.83/1.86  tff(c_614, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_613])).
% 4.83/1.86  tff(c_642, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_614])).
% 4.83/1.86  tff(c_645, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_642])).
% 4.83/1.86  tff(c_647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_645])).
% 4.83/1.86  tff(c_648, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_613])).
% 4.83/1.86  tff(c_650, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_648])).
% 4.83/1.86  tff(c_653, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_650])).
% 4.83/1.86  tff(c_656, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_653])).
% 4.83/1.86  tff(c_658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_656])).
% 4.83/1.86  tff(c_659, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_648])).
% 4.83/1.86  tff(c_663, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_659, c_6])).
% 4.83/1.86  tff(c_666, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_663])).
% 4.83/1.86  tff(c_668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_666])).
% 4.83/1.86  tff(c_669, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_541])).
% 4.83/1.86  tff(c_843, plain, (![C_241, D_242, B_243, A_244]: (~r1_tsep_1(C_241, D_242) | r1_tsep_1(B_243, D_242) | ~m1_pre_topc(B_243, C_241) | ~m1_pre_topc(D_242, A_244) | v2_struct_0(D_242) | ~m1_pre_topc(C_241, A_244) | v2_struct_0(C_241) | ~m1_pre_topc(B_243, A_244) | v2_struct_0(B_243) | ~l1_pre_topc(A_244) | ~v2_pre_topc(A_244) | v2_struct_0(A_244))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.83/1.86  tff(c_853, plain, (![B_243, A_244]: (r1_tsep_1(B_243, '#skF_4') | ~m1_pre_topc(B_243, '#skF_2') | ~m1_pre_topc('#skF_4', A_244) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', A_244) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_243, A_244) | v2_struct_0(B_243) | ~l1_pre_topc(A_244) | ~v2_pre_topc(A_244) | v2_struct_0(A_244))), inference(resolution, [status(thm)], [c_669, c_843])).
% 4.83/1.86  tff(c_869, plain, (![B_245, A_246]: (r1_tsep_1(B_245, '#skF_4') | ~m1_pre_topc(B_245, '#skF_2') | ~m1_pre_topc('#skF_4', A_246) | ~m1_pre_topc('#skF_2', A_246) | ~m1_pre_topc(B_245, A_246) | v2_struct_0(B_245) | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(negUnitSimplification, [status(thm)], [c_32, c_24, c_853])).
% 4.83/1.86  tff(c_871, plain, (![B_245]: (r1_tsep_1(B_245, '#skF_4') | ~m1_pre_topc(B_245, '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_245, '#skF_1') | v2_struct_0(B_245) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_869])).
% 4.83/1.86  tff(c_874, plain, (![B_245]: (r1_tsep_1(B_245, '#skF_4') | ~m1_pre_topc(B_245, '#skF_2') | ~m1_pre_topc(B_245, '#skF_1') | v2_struct_0(B_245) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_871])).
% 4.83/1.86  tff(c_876, plain, (![B_247]: (r1_tsep_1(B_247, '#skF_4') | ~m1_pre_topc(B_247, '#skF_2') | ~m1_pre_topc(B_247, '#skF_1') | v2_struct_0(B_247))), inference(negUnitSimplification, [status(thm)], [c_38, c_874])).
% 4.83/1.86  tff(c_907, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_876, c_47])).
% 4.83/1.86  tff(c_941, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_918, c_907])).
% 4.83/1.86  tff(c_942, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_941])).
% 4.83/1.86  tff(c_945, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_942])).
% 4.83/1.86  tff(c_948, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_945])).
% 4.83/1.86  tff(c_950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_948])).
% 4.83/1.86  tff(c_951, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_941])).
% 4.83/1.86  tff(c_969, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_951])).
% 4.83/1.86  tff(c_972, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_969])).
% 4.83/1.86  tff(c_974, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_972])).
% 4.83/1.86  tff(c_976, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 4.83/1.86  tff(c_1224, plain, (![C_316, D_317, B_318, A_319]: (~r1_tsep_1(C_316, D_317) | r1_tsep_1(D_317, B_318) | ~m1_pre_topc(B_318, C_316) | ~m1_pre_topc(D_317, A_319) | v2_struct_0(D_317) | ~m1_pre_topc(C_316, A_319) | v2_struct_0(C_316) | ~m1_pre_topc(B_318, A_319) | v2_struct_0(B_318) | ~l1_pre_topc(A_319) | ~v2_pre_topc(A_319) | v2_struct_0(A_319))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.83/1.86  tff(c_1228, plain, (![B_318, A_319]: (r1_tsep_1('#skF_4', B_318) | ~m1_pre_topc(B_318, k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_4', A_319) | v2_struct_0('#skF_4') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_319) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc(B_318, A_319) | v2_struct_0(B_318) | ~l1_pre_topc(A_319) | ~v2_pre_topc(A_319) | v2_struct_0(A_319))), inference(resolution, [status(thm)], [c_976, c_1224])).
% 4.83/1.86  tff(c_1236, plain, (![B_318, A_319]: (r1_tsep_1('#skF_4', B_318) | ~m1_pre_topc(B_318, k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_4', A_319) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_319) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc(B_318, A_319) | v2_struct_0(B_318) | ~l1_pre_topc(A_319) | ~v2_pre_topc(A_319) | v2_struct_0(A_319))), inference(negUnitSimplification, [status(thm)], [c_24, c_1228])).
% 4.83/1.86  tff(c_1374, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1236])).
% 4.83/1.86  tff(c_1377, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1374, c_6])).
% 4.83/1.86  tff(c_1380, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_1377])).
% 4.83/1.86  tff(c_1382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_1380])).
% 4.83/1.86  tff(c_1384, plain, (~v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1236])).
% 4.83/1.86  tff(c_1045, plain, (![D_280, C_281, B_282, A_283]: (~r1_tsep_1(D_280, C_281) | r1_tsep_1(D_280, B_282) | ~m1_pre_topc(B_282, C_281) | ~m1_pre_topc(D_280, A_283) | v2_struct_0(D_280) | ~m1_pre_topc(C_281, A_283) | v2_struct_0(C_281) | ~m1_pre_topc(B_282, A_283) | v2_struct_0(B_282) | ~l1_pre_topc(A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.83/1.86  tff(c_1051, plain, (![B_282, A_283]: (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), B_282) | ~m1_pre_topc(B_282, '#skF_4') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_283) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_4', A_283) | v2_struct_0('#skF_4') | ~m1_pre_topc(B_282, A_283) | v2_struct_0(B_282) | ~l1_pre_topc(A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283))), inference(resolution, [status(thm)], [c_976, c_1045])).
% 4.83/1.86  tff(c_1062, plain, (![B_282, A_283]: (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), B_282) | ~m1_pre_topc(B_282, '#skF_4') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_283) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_4', A_283) | ~m1_pre_topc(B_282, A_283) | v2_struct_0(B_282) | ~l1_pre_topc(A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283))), inference(negUnitSimplification, [status(thm)], [c_24, c_1051])).
% 4.83/1.86  tff(c_1176, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1062])).
% 4.83/1.86  tff(c_1179, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1176, c_6])).
% 4.83/1.86  tff(c_1182, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_1179])).
% 4.83/1.86  tff(c_1184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_1182])).
% 4.83/1.86  tff(c_1186, plain, (~v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1062])).
% 4.83/1.86  tff(c_975, plain, (r1_tsep_1('#skF_4', '#skF_2') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 4.83/1.86  tff(c_977, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_975])).
% 4.83/1.86  tff(c_1053, plain, (![B_282, A_283]: (r1_tsep_1('#skF_4', B_282) | ~m1_pre_topc(B_282, '#skF_3') | ~m1_pre_topc('#skF_4', A_283) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_283) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_282, A_283) | v2_struct_0(B_282) | ~l1_pre_topc(A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283))), inference(resolution, [status(thm)], [c_977, c_1045])).
% 4.83/1.86  tff(c_1066, plain, (![B_284, A_285]: (r1_tsep_1('#skF_4', B_284) | ~m1_pre_topc(B_284, '#skF_3') | ~m1_pre_topc('#skF_4', A_285) | ~m1_pre_topc('#skF_3', A_285) | ~m1_pre_topc(B_284, A_285) | v2_struct_0(B_284) | ~l1_pre_topc(A_285) | ~v2_pre_topc(A_285) | v2_struct_0(A_285))), inference(negUnitSimplification, [status(thm)], [c_28, c_24, c_1053])).
% 4.83/1.86  tff(c_1068, plain, (![B_284]: (r1_tsep_1('#skF_4', B_284) | ~m1_pre_topc(B_284, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_284, '#skF_1') | v2_struct_0(B_284) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_1066])).
% 4.83/1.86  tff(c_1071, plain, (![B_284]: (r1_tsep_1('#skF_4', B_284) | ~m1_pre_topc(B_284, '#skF_3') | ~m1_pre_topc(B_284, '#skF_1') | v2_struct_0(B_284) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_1068])).
% 4.83/1.86  tff(c_1094, plain, (![B_290]: (r1_tsep_1('#skF_4', B_290) | ~m1_pre_topc(B_290, '#skF_3') | ~m1_pre_topc(B_290, '#skF_1') | v2_struct_0(B_290))), inference(negUnitSimplification, [status(thm)], [c_38, c_1071])).
% 4.83/1.86  tff(c_46, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.83/1.86  tff(c_980, plain, (~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_976, c_46])).
% 4.83/1.86  tff(c_1118, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1094, c_980])).
% 4.83/1.86  tff(c_1119, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1118])).
% 4.83/1.86  tff(c_1122, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_1119])).
% 4.83/1.86  tff(c_1125, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_1122])).
% 4.83/1.86  tff(c_1127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_1125])).
% 4.83/1.86  tff(c_1128, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1118])).
% 4.83/1.86  tff(c_1165, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1128])).
% 4.83/1.86  tff(c_1168, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_1165])).
% 4.83/1.86  tff(c_1171, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_1168])).
% 4.83/1.86  tff(c_1173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_1171])).
% 4.83/1.86  tff(c_1174, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1128])).
% 4.83/1.86  tff(c_1187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1186, c_1174])).
% 4.83/1.86  tff(c_1188, plain, (r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_975])).
% 4.83/1.86  tff(c_1309, plain, (![D_330, C_331, B_332, A_333]: (~r1_tsep_1(D_330, C_331) | r1_tsep_1(D_330, B_332) | ~m1_pre_topc(B_332, C_331) | ~m1_pre_topc(D_330, A_333) | v2_struct_0(D_330) | ~m1_pre_topc(C_331, A_333) | v2_struct_0(C_331) | ~m1_pre_topc(B_332, A_333) | v2_struct_0(B_332) | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333) | v2_struct_0(A_333))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.83/1.86  tff(c_1319, plain, (![B_332, A_333]: (r1_tsep_1('#skF_4', B_332) | ~m1_pre_topc(B_332, '#skF_2') | ~m1_pre_topc('#skF_4', A_333) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', A_333) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_332, A_333) | v2_struct_0(B_332) | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333) | v2_struct_0(A_333))), inference(resolution, [status(thm)], [c_1188, c_1309])).
% 4.83/1.86  tff(c_1335, plain, (![B_334, A_335]: (r1_tsep_1('#skF_4', B_334) | ~m1_pre_topc(B_334, '#skF_2') | ~m1_pre_topc('#skF_4', A_335) | ~m1_pre_topc('#skF_2', A_335) | ~m1_pre_topc(B_334, A_335) | v2_struct_0(B_334) | ~l1_pre_topc(A_335) | ~v2_pre_topc(A_335) | v2_struct_0(A_335))), inference(negUnitSimplification, [status(thm)], [c_32, c_24, c_1319])).
% 4.83/1.86  tff(c_1337, plain, (![B_334]: (r1_tsep_1('#skF_4', B_334) | ~m1_pre_topc(B_334, '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_334, '#skF_1') | v2_struct_0(B_334) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_1335])).
% 4.83/1.86  tff(c_1340, plain, (![B_334]: (r1_tsep_1('#skF_4', B_334) | ~m1_pre_topc(B_334, '#skF_2') | ~m1_pre_topc(B_334, '#skF_1') | v2_struct_0(B_334) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_22, c_1337])).
% 4.83/1.86  tff(c_1342, plain, (![B_336]: (r1_tsep_1('#skF_4', B_336) | ~m1_pre_topc(B_336, '#skF_2') | ~m1_pre_topc(B_336, '#skF_1') | v2_struct_0(B_336))), inference(negUnitSimplification, [status(thm)], [c_38, c_1340])).
% 4.83/1.86  tff(c_1190, plain, (~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_44])).
% 4.83/1.86  tff(c_1369, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1342, c_1190])).
% 4.83/1.86  tff(c_1385, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1384, c_1369])).
% 4.83/1.86  tff(c_1386, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1385])).
% 4.83/1.86  tff(c_1414, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2, c_1386])).
% 4.83/1.86  tff(c_1417, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_26, c_1414])).
% 4.83/1.86  tff(c_1419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_1417])).
% 4.83/1.86  tff(c_1420, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_1385])).
% 4.83/1.86  tff(c_1424, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1420])).
% 4.83/1.86  tff(c_1427, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_26, c_1424])).
% 4.83/1.86  tff(c_1429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_28, c_20, c_1427])).
% 4.83/1.86  tff(c_1431, plain, (r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_44])).
% 4.83/1.86  tff(c_1434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1431, c_976, c_46])).
% 4.83/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.83/1.86  
% 4.83/1.86  Inference rules
% 4.83/1.86  ----------------------
% 4.83/1.86  #Ref     : 0
% 4.83/1.86  #Sup     : 224
% 4.83/1.86  #Fact    : 0
% 4.83/1.86  #Define  : 0
% 4.83/1.86  #Split   : 29
% 4.83/1.86  #Chain   : 0
% 4.83/1.86  #Close   : 0
% 4.83/1.86  
% 4.83/1.86  Ordering : KBO
% 4.83/1.86  
% 4.83/1.86  Simplification rules
% 4.83/1.86  ----------------------
% 4.83/1.86  #Subsume      : 18
% 4.83/1.86  #Demod        : 197
% 4.83/1.86  #Tautology    : 9
% 4.83/1.86  #SimpNegUnit  : 196
% 4.83/1.86  #BackRed      : 0
% 4.83/1.86  
% 4.83/1.86  #Partial instantiations: 0
% 4.83/1.86  #Strategies tried      : 1
% 4.83/1.86  
% 4.83/1.86  Timing (in seconds)
% 4.83/1.86  ----------------------
% 5.03/1.87  Preprocessing        : 0.30
% 5.03/1.87  Parsing              : 0.17
% 5.03/1.87  CNF conversion       : 0.03
% 5.03/1.87  Main loop            : 0.70
% 5.03/1.87  Inferencing          : 0.23
% 5.03/1.87  Reduction            : 0.17
% 5.03/1.87  Demodulation         : 0.11
% 5.03/1.87  BG Simplification    : 0.03
% 5.03/1.87  Subsumption          : 0.23
% 5.03/1.87  Abstraction          : 0.03
% 5.03/1.87  MUC search           : 0.00
% 5.03/1.87  Cooper               : 0.00
% 5.03/1.87  Total                : 1.12
% 5.03/1.87  Index Insertion      : 0.00
% 5.03/1.87  Index Deletion       : 0.00
% 5.03/1.87  Index Matching       : 0.00
% 5.03/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
