%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:47 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 277 expanded)
%              Number of leaves         :   15 ( 119 expanded)
%              Depth                    :    6
%              Number of atoms          :  309 (2103 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_112,negated_conjecture,(
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

tff(f_71,axiom,(
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
                 => ( ~ r1_tsep_1(B,C)
                   => ( ( ~ r1_tsep_1(k2_tsep_1(A,B,C),D)
                       => ( ~ r1_tsep_1(B,D)
                          & ~ r1_tsep_1(C,D) ) )
                      & ( ~ r1_tsep_1(D,k2_tsep_1(A,B,C))
                       => ( ~ r1_tsep_1(D,B)
                          & ~ r1_tsep_1(D,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tmap_1)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_18,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_14,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_10,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_20,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_16,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_12,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_36,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_39,plain,(
    r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_48,plain,(
    ! [D_31,B_32,A_33,C_34] :
      ( ~ r1_tsep_1(D_31,B_32)
      | r1_tsep_1(D_31,k2_tsep_1(A_33,B_32,C_34))
      | r1_tsep_1(B_32,C_34)
      | ~ m1_pre_topc(D_31,A_33)
      | v2_struct_0(D_31)
      | ~ m1_pre_topc(C_34,A_33)
      | v2_struct_0(C_34)
      | ~ m1_pre_topc(B_32,A_33)
      | v2_struct_0(B_32)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_2','#skF_4')
    | ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_38,plain,(
    ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_51,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_2')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_38])).

tff(c_54,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_16,c_12,c_39,c_51])).

tff(c_56,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_22,c_18,c_14,c_10,c_54])).

tff(c_57,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_59,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_68,plain,(
    ! [C_39,D_40,A_41,B_42] :
      ( ~ r1_tsep_1(C_39,D_40)
      | r1_tsep_1(k2_tsep_1(A_41,B_42,C_39),D_40)
      | r1_tsep_1(B_42,C_39)
      | ~ m1_pre_topc(D_40,A_41)
      | v2_struct_0(D_40)
      | ~ m1_pre_topc(C_39,A_41)
      | v2_struct_0(C_39)
      | ~ m1_pre_topc(B_42,A_41)
      | v2_struct_0(B_42)
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,
    ( ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_37,plain,(
    ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_71,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_37])).

tff(c_74,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_16,c_12,c_59,c_71])).

tff(c_76,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_22,c_18,c_14,c_10,c_74])).

tff(c_77,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_79,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_96,plain,(
    ! [D_51,C_52,A_53,B_54] :
      ( ~ r1_tsep_1(D_51,C_52)
      | r1_tsep_1(D_51,k2_tsep_1(A_53,B_54,C_52))
      | r1_tsep_1(B_54,C_52)
      | ~ m1_pre_topc(D_51,A_53)
      | v2_struct_0(D_51)
      | ~ m1_pre_topc(C_52,A_53)
      | v2_struct_0(C_52)
      | ~ m1_pre_topc(B_54,A_53)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_99,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_96,c_38])).

tff(c_102,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_16,c_12,c_79,c_99])).

tff(c_104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_22,c_18,c_14,c_10,c_102])).

tff(c_105,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_107,plain,(
    ! [B_55,D_56,A_57,C_58] :
      ( ~ r1_tsep_1(B_55,D_56)
      | r1_tsep_1(k2_tsep_1(A_57,B_55,C_58),D_56)
      | r1_tsep_1(B_55,C_58)
      | ~ m1_pre_topc(D_56,A_57)
      | v2_struct_0(D_56)
      | ~ m1_pre_topc(C_58,A_57)
      | v2_struct_0(C_58)
      | ~ m1_pre_topc(B_55,A_57)
      | v2_struct_0(B_55)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_110,plain,
    ( ~ r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_107,c_37])).

tff(c_113,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_16,c_12,c_105,c_110])).

tff(c_115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_22,c_18,c_14,c_10,c_113])).

tff(c_116,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_118,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_129,plain,(
    ! [C_67,D_68,A_69,B_70] :
      ( ~ r1_tsep_1(C_67,D_68)
      | r1_tsep_1(k2_tsep_1(A_69,B_70,C_67),D_68)
      | r1_tsep_1(B_70,C_67)
      | ~ m1_pre_topc(D_68,A_69)
      | v2_struct_0(D_68)
      | ~ m1_pre_topc(C_67,A_69)
      | v2_struct_0(C_67)
      | ~ m1_pre_topc(B_70,A_69)
      | v2_struct_0(B_70)
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_132,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_129,c_37])).

tff(c_135,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_16,c_12,c_118,c_132])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_22,c_18,c_14,c_10,c_135])).

tff(c_138,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_143,plain,(
    ! [B_75,D_76,A_77,C_78] :
      ( ~ r1_tsep_1(B_75,D_76)
      | r1_tsep_1(k2_tsep_1(A_77,B_75,C_78),D_76)
      | r1_tsep_1(B_75,C_78)
      | ~ m1_pre_topc(D_76,A_77)
      | v2_struct_0(D_76)
      | ~ m1_pre_topc(C_78,A_77)
      | v2_struct_0(C_78)
      | ~ m1_pre_topc(B_75,A_77)
      | v2_struct_0(B_75)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_146,plain,
    ( ~ r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_143,c_37])).

tff(c_149,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_16,c_12,c_138,c_146])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_22,c_18,c_14,c_10,c_149])).

tff(c_153,plain,(
    r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_152,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_155,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_167,plain,(
    ! [D_91,C_92,A_93,B_94] :
      ( ~ r1_tsep_1(D_91,C_92)
      | r1_tsep_1(D_91,k2_tsep_1(A_93,B_94,C_92))
      | r1_tsep_1(B_94,C_92)
      | ~ m1_pre_topc(D_91,A_93)
      | v2_struct_0(D_91)
      | ~ m1_pre_topc(C_92,A_93)
      | v2_struct_0(C_92)
      | ~ m1_pre_topc(B_94,A_93)
      | v2_struct_0(B_94)
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,
    ( ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_154,plain,(
    ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_170,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_167,c_154])).

tff(c_173,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_16,c_12,c_155,c_170])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_22,c_18,c_14,c_10,c_173])).

tff(c_176,plain,(
    r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_189,plain,(
    ! [D_103,B_104,A_105,C_106] :
      ( ~ r1_tsep_1(D_103,B_104)
      | r1_tsep_1(D_103,k2_tsep_1(A_105,B_104,C_106))
      | r1_tsep_1(B_104,C_106)
      | ~ m1_pre_topc(D_103,A_105)
      | v2_struct_0(D_103)
      | ~ m1_pre_topc(C_106,A_105)
      | v2_struct_0(C_106)
      | ~ m1_pre_topc(B_104,A_105)
      | v2_struct_0(B_104)
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_192,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_2')
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_189,c_154])).

tff(c_195,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_20,c_16,c_12,c_176,c_192])).

tff(c_197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_22,c_18,c_14,c_10,c_195])).

tff(c_198,plain,(
    ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n025.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:02:35 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.26  
% 2.37/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.27  %$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.37/1.27  
% 2.37/1.27  %Foreground sorts:
% 2.37/1.27  
% 2.37/1.27  
% 2.37/1.27  %Background operators:
% 2.37/1.27  
% 2.37/1.27  
% 2.37/1.27  %Foreground operators:
% 2.37/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.37/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.37/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.27  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.37/1.27  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 2.37/1.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.37/1.27  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.37/1.27  
% 2.37/1.28  tff(f_112, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(B, C) => (((r1_tsep_1(B, D) | r1_tsep_1(C, D)) => r1_tsep_1(k2_tsep_1(A, B, C), D)) & ((r1_tsep_1(D, B) | r1_tsep_1(D, C)) => r1_tsep_1(D, k2_tsep_1(A, B, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tmap_1)).
% 2.37/1.28  tff(f_71, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(B, C) => ((~r1_tsep_1(k2_tsep_1(A, B, C), D) => (~r1_tsep_1(B, D) & ~r1_tsep_1(C, D))) & (~r1_tsep_1(D, k2_tsep_1(A, B, C)) => (~r1_tsep_1(D, B) & ~r1_tsep_1(D, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tmap_1)).
% 2.37/1.28  tff(c_28, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.37/1.29  tff(c_22, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.37/1.29  tff(c_18, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.37/1.29  tff(c_14, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.37/1.29  tff(c_10, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.37/1.29  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.37/1.29  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.37/1.29  tff(c_20, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.37/1.29  tff(c_16, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.37/1.29  tff(c_12, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.37/1.29  tff(c_36, plain, (r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.37/1.29  tff(c_39, plain, (r1_tsep_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_36])).
% 2.37/1.29  tff(c_48, plain, (![D_31, B_32, A_33, C_34]: (~r1_tsep_1(D_31, B_32) | r1_tsep_1(D_31, k2_tsep_1(A_33, B_32, C_34)) | r1_tsep_1(B_32, C_34) | ~m1_pre_topc(D_31, A_33) | v2_struct_0(D_31) | ~m1_pre_topc(C_34, A_33) | v2_struct_0(C_34) | ~m1_pre_topc(B_32, A_33) | v2_struct_0(B_32) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.29  tff(c_32, plain, (r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_2', '#skF_4') | ~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.37/1.29  tff(c_38, plain, (~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.37/1.29  tff(c_51, plain, (~r1_tsep_1('#skF_4', '#skF_2') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_38])).
% 2.37/1.29  tff(c_54, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20, c_16, c_12, c_39, c_51])).
% 2.37/1.29  tff(c_56, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_22, c_18, c_14, c_10, c_54])).
% 2.37/1.29  tff(c_57, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 2.37/1.29  tff(c_59, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_57])).
% 2.37/1.29  tff(c_68, plain, (![C_39, D_40, A_41, B_42]: (~r1_tsep_1(C_39, D_40) | r1_tsep_1(k2_tsep_1(A_41, B_42, C_39), D_40) | r1_tsep_1(B_42, C_39) | ~m1_pre_topc(D_40, A_41) | v2_struct_0(D_40) | ~m1_pre_topc(C_39, A_41) | v2_struct_0(C_39) | ~m1_pre_topc(B_42, A_41) | v2_struct_0(B_42) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.29  tff(c_34, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.37/1.29  tff(c_37, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_34])).
% 2.37/1.29  tff(c_71, plain, (~r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_37])).
% 2.37/1.29  tff(c_74, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20, c_16, c_12, c_59, c_71])).
% 2.37/1.29  tff(c_76, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_22, c_18, c_14, c_10, c_74])).
% 2.37/1.29  tff(c_77, plain, (r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_57])).
% 2.37/1.29  tff(c_79, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_77])).
% 2.37/1.29  tff(c_96, plain, (![D_51, C_52, A_53, B_54]: (~r1_tsep_1(D_51, C_52) | r1_tsep_1(D_51, k2_tsep_1(A_53, B_54, C_52)) | r1_tsep_1(B_54, C_52) | ~m1_pre_topc(D_51, A_53) | v2_struct_0(D_51) | ~m1_pre_topc(C_52, A_53) | v2_struct_0(C_52) | ~m1_pre_topc(B_54, A_53) | v2_struct_0(B_54) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.29  tff(c_99, plain, (~r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_96, c_38])).
% 2.37/1.29  tff(c_102, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20, c_16, c_12, c_79, c_99])).
% 2.37/1.29  tff(c_104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_22, c_18, c_14, c_10, c_102])).
% 2.37/1.29  tff(c_105, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_77])).
% 2.37/1.29  tff(c_107, plain, (![B_55, D_56, A_57, C_58]: (~r1_tsep_1(B_55, D_56) | r1_tsep_1(k2_tsep_1(A_57, B_55, C_58), D_56) | r1_tsep_1(B_55, C_58) | ~m1_pre_topc(D_56, A_57) | v2_struct_0(D_56) | ~m1_pre_topc(C_58, A_57) | v2_struct_0(C_58) | ~m1_pre_topc(B_55, A_57) | v2_struct_0(B_55) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.29  tff(c_110, plain, (~r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_107, c_37])).
% 2.37/1.29  tff(c_113, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20, c_16, c_12, c_105, c_110])).
% 2.37/1.29  tff(c_115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_22, c_18, c_14, c_10, c_113])).
% 2.37/1.29  tff(c_116, plain, (r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 2.37/1.29  tff(c_118, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_116])).
% 2.37/1.29  tff(c_129, plain, (![C_67, D_68, A_69, B_70]: (~r1_tsep_1(C_67, D_68) | r1_tsep_1(k2_tsep_1(A_69, B_70, C_67), D_68) | r1_tsep_1(B_70, C_67) | ~m1_pre_topc(D_68, A_69) | v2_struct_0(D_68) | ~m1_pre_topc(C_67, A_69) | v2_struct_0(C_67) | ~m1_pre_topc(B_70, A_69) | v2_struct_0(B_70) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.29  tff(c_132, plain, (~r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_129, c_37])).
% 2.37/1.29  tff(c_135, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20, c_16, c_12, c_118, c_132])).
% 2.37/1.29  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_22, c_18, c_14, c_10, c_135])).
% 2.37/1.29  tff(c_138, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_116])).
% 2.37/1.29  tff(c_143, plain, (![B_75, D_76, A_77, C_78]: (~r1_tsep_1(B_75, D_76) | r1_tsep_1(k2_tsep_1(A_77, B_75, C_78), D_76) | r1_tsep_1(B_75, C_78) | ~m1_pre_topc(D_76, A_77) | v2_struct_0(D_76) | ~m1_pre_topc(C_78, A_77) | v2_struct_0(C_78) | ~m1_pre_topc(B_75, A_77) | v2_struct_0(B_75) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.29  tff(c_146, plain, (~r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_143, c_37])).
% 2.37/1.29  tff(c_149, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20, c_16, c_12, c_138, c_146])).
% 2.37/1.29  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_22, c_18, c_14, c_10, c_149])).
% 2.37/1.29  tff(c_153, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 2.37/1.29  tff(c_152, plain, (r1_tsep_1('#skF_4', '#skF_2') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 2.37/1.29  tff(c_155, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_152])).
% 2.37/1.29  tff(c_167, plain, (![D_91, C_92, A_93, B_94]: (~r1_tsep_1(D_91, C_92) | r1_tsep_1(D_91, k2_tsep_1(A_93, B_94, C_92)) | r1_tsep_1(B_94, C_92) | ~m1_pre_topc(D_91, A_93) | v2_struct_0(D_91) | ~m1_pre_topc(C_92, A_93) | v2_struct_0(C_92) | ~m1_pre_topc(B_94, A_93) | v2_struct_0(B_94) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.29  tff(c_30, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.37/1.29  tff(c_154, plain, (~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_30])).
% 2.37/1.29  tff(c_170, plain, (~r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_167, c_154])).
% 2.37/1.29  tff(c_173, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20, c_16, c_12, c_155, c_170])).
% 2.37/1.29  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_22, c_18, c_14, c_10, c_173])).
% 2.37/1.29  tff(c_176, plain, (r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_152])).
% 2.37/1.29  tff(c_189, plain, (![D_103, B_104, A_105, C_106]: (~r1_tsep_1(D_103, B_104) | r1_tsep_1(D_103, k2_tsep_1(A_105, B_104, C_106)) | r1_tsep_1(B_104, C_106) | ~m1_pre_topc(D_103, A_105) | v2_struct_0(D_103) | ~m1_pre_topc(C_106, A_105) | v2_struct_0(C_106) | ~m1_pre_topc(B_104, A_105) | v2_struct_0(B_104) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.29  tff(c_192, plain, (~r1_tsep_1('#skF_4', '#skF_2') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_189, c_154])).
% 2.37/1.29  tff(c_195, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_20, c_16, c_12, c_176, c_192])).
% 2.37/1.29  tff(c_197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_22, c_18, c_14, c_10, c_195])).
% 2.37/1.29  tff(c_198, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 2.37/1.29  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_153, c_198])).
% 2.37/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.29  
% 2.37/1.29  Inference rules
% 2.37/1.29  ----------------------
% 2.37/1.29  #Ref     : 0
% 2.37/1.29  #Sup     : 15
% 2.37/1.29  #Fact    : 0
% 2.37/1.29  #Define  : 0
% 2.37/1.29  #Split   : 9
% 2.37/1.29  #Chain   : 0
% 2.37/1.29  #Close   : 0
% 2.37/1.29  
% 2.37/1.29  Ordering : KBO
% 2.37/1.29  
% 2.37/1.29  Simplification rules
% 2.37/1.29  ----------------------
% 2.37/1.29  #Subsume      : 6
% 2.37/1.29  #Demod        : 88
% 2.37/1.29  #Tautology    : 4
% 2.37/1.29  #SimpNegUnit  : 17
% 2.37/1.29  #BackRed      : 0
% 2.37/1.29  
% 2.37/1.29  #Partial instantiations: 0
% 2.37/1.29  #Strategies tried      : 1
% 2.37/1.29  
% 2.37/1.29  Timing (in seconds)
% 2.37/1.29  ----------------------
% 2.37/1.29  Preprocessing        : 0.29
% 2.37/1.29  Parsing              : 0.16
% 2.37/1.29  CNF conversion       : 0.02
% 2.37/1.29  Main loop            : 0.26
% 2.37/1.29  Inferencing          : 0.11
% 2.37/1.29  Reduction            : 0.07
% 2.37/1.29  Demodulation         : 0.05
% 2.37/1.29  BG Simplification    : 0.01
% 2.37/1.29  Subsumption          : 0.05
% 2.37/1.29  Abstraction          : 0.01
% 2.37/1.29  MUC search           : 0.00
% 2.37/1.29  Cooper               : 0.00
% 2.37/1.29  Total                : 0.58
% 2.37/1.29  Index Insertion      : 0.00
% 2.37/1.29  Index Deletion       : 0.00
% 2.37/1.29  Index Matching       : 0.00
% 2.37/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
