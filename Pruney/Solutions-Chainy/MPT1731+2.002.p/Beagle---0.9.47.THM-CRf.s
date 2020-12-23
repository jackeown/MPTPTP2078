%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:46 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 663 expanded)
%              Number of leaves         :   15 ( 240 expanded)
%              Depth                    :   10
%              Number of atoms          :  546 (5915 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tsep_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
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
                   => ( ( r1_tsep_1(k1_tsep_1(A,B,C),D)
                       => ( r1_tsep_1(B,D)
                          & r1_tsep_1(C,D) ) )
                      & ( ( r1_tsep_1(B,D)
                          & r1_tsep_1(C,D) )
                       => r1_tsep_1(k1_tsep_1(A,B,C),D) )
                      & ( r1_tsep_1(D,k1_tsep_1(A,B,C))
                       => ( r1_tsep_1(D,B)
                          & r1_tsep_1(D,C) ) )
                      & ( ( r1_tsep_1(D,B)
                          & r1_tsep_1(D,C) )
                       => r1_tsep_1(D,k1_tsep_1(A,B,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tmap_1)).

tff(f_82,axiom,(
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
                 => ( ~ ( ~ r1_tsep_1(k1_tsep_1(A,B,C),D)
                        & r1_tsep_1(B,D)
                        & r1_tsep_1(C,D) )
                    & ~ ( ~ ( r1_tsep_1(B,D)
                            & r1_tsep_1(C,D) )
                        & r1_tsep_1(k1_tsep_1(A,B,C),D) )
                    & ~ ( ~ r1_tsep_1(D,k1_tsep_1(A,B,C))
                        & r1_tsep_1(D,B)
                        & r1_tsep_1(D,C) )
                    & ~ ( ~ ( r1_tsep_1(D,B)
                            & r1_tsep_1(D,C) )
                        & r1_tsep_1(D,k1_tsep_1(A,B,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tmap_1)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_20,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_16,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_22,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_18,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_14,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_98,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_103,plain,(
    r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_78,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_104,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_141,plain,(
    ! [D_47,C_48,B_49,A_50] :
      ( ~ r1_tsep_1(D_47,C_48)
      | ~ r1_tsep_1(D_47,B_49)
      | r1_tsep_1(D_47,k1_tsep_1(A_50,B_49,C_48))
      | ~ m1_pre_topc(D_47,A_50)
      | v2_struct_0(D_47)
      | ~ m1_pre_topc(C_48,A_50)
      | v2_struct_0(C_48)
      | ~ m1_pre_topc(B_49,A_50)
      | v2_struct_0(B_49)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_4','#skF_3')
    | ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_108,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_104,c_38])).

tff(c_109,plain,(
    ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_158,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_3')
    | ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_141,c_109])).

tff(c_165,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_18,c_14,c_103,c_104,c_158])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_20,c_16,c_165])).

tff(c_169,plain,(
    r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_168,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_170,plain,(
    r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_32,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_2','#skF_4')
    | ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tsep_1('#skF_4','#skF_3')
    | ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_177,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_103,c_104,c_170,c_32])).

tff(c_178,plain,(
    ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_187,plain,(
    ! [B_55,D_56,A_57,C_58] :
      ( r1_tsep_1(B_55,D_56)
      | ~ r1_tsep_1(k1_tsep_1(A_57,B_55,C_58),D_56)
      | ~ m1_pre_topc(D_56,A_57)
      | v2_struct_0(D_56)
      | ~ m1_pre_topc(C_58,A_57)
      | v2_struct_0(C_58)
      | ~ m1_pre_topc(B_55,A_57)
      | v2_struct_0(B_55)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_190,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_170,c_187])).

tff(c_193,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_18,c_14,c_190])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_20,c_16,c_178,c_193])).

tff(c_196,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_222,plain,(
    ! [C_71,D_72,A_73,B_74] :
      ( r1_tsep_1(C_71,D_72)
      | ~ r1_tsep_1(k1_tsep_1(A_73,B_74,C_71),D_72)
      | ~ m1_pre_topc(D_72,A_73)
      | v2_struct_0(D_72)
      | ~ m1_pre_topc(C_71,A_73)
      | v2_struct_0(C_71)
      | ~ m1_pre_topc(B_74,A_73)
      | v2_struct_0(B_74)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_225,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_170,c_222])).

tff(c_228,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_18,c_14,c_225])).

tff(c_230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_20,c_16,c_196,c_228])).

tff(c_232,plain,(
    ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_42,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_2','#skF_4')
    | ~ r1_tsep_1('#skF_4','#skF_3')
    | ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_236,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_103,c_104,c_42])).

tff(c_237,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_236])).

tff(c_231,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_279,plain,(
    ! [C_95,D_96,B_97,A_98] :
      ( ~ r1_tsep_1(C_95,D_96)
      | ~ r1_tsep_1(B_97,D_96)
      | r1_tsep_1(k1_tsep_1(A_98,B_97,C_95),D_96)
      | ~ m1_pre_topc(D_96,A_98)
      | v2_struct_0(D_96)
      | ~ m1_pre_topc(C_95,A_98)
      | v2_struct_0(C_95)
      | ~ m1_pre_topc(B_97,A_98)
      | v2_struct_0(B_97)
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_296,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_279,c_232])).

tff(c_303,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_18,c_14,c_237,c_231,c_296])).

tff(c_305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_20,c_16,c_303])).

tff(c_307,plain,(
    ~ r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_306,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_308,plain,(
    r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_306])).

tff(c_68,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_2','#skF_4')
    | ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_319,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_68])).

tff(c_320,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_319])).

tff(c_321,plain,(
    ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_320])).

tff(c_334,plain,(
    ! [B_111,D_112,A_113,C_114] :
      ( r1_tsep_1(B_111,D_112)
      | ~ r1_tsep_1(k1_tsep_1(A_113,B_111,C_114),D_112)
      | ~ m1_pre_topc(D_112,A_113)
      | v2_struct_0(D_112)
      | ~ m1_pre_topc(C_114,A_113)
      | v2_struct_0(C_114)
      | ~ m1_pre_topc(B_111,A_113)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_337,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_308,c_334])).

tff(c_340,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_18,c_14,c_337])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_20,c_16,c_321,c_340])).

tff(c_343,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_345,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_358,plain,(
    ! [C_127,D_128,A_129,B_130] :
      ( r1_tsep_1(C_127,D_128)
      | ~ r1_tsep_1(k1_tsep_1(A_129,B_130,C_127),D_128)
      | ~ m1_pre_topc(D_128,A_129)
      | v2_struct_0(D_128)
      | ~ m1_pre_topc(C_127,A_129)
      | v2_struct_0(C_127)
      | ~ m1_pre_topc(B_130,A_129)
      | v2_struct_0(B_130)
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_361,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_308,c_358])).

tff(c_364,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_18,c_14,c_361])).

tff(c_366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_20,c_16,c_345,c_364])).

tff(c_367,plain,(
    r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_387,plain,(
    ! [D_139,C_140,A_141,B_142] :
      ( r1_tsep_1(D_139,C_140)
      | ~ r1_tsep_1(D_139,k1_tsep_1(A_141,B_142,C_140))
      | ~ m1_pre_topc(D_139,A_141)
      | v2_struct_0(D_139)
      | ~ m1_pre_topc(C_140,A_141)
      | v2_struct_0(C_140)
      | ~ m1_pre_topc(B_142,A_141)
      | v2_struct_0(B_142)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_390,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_367,c_387])).

tff(c_393,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_18,c_14,c_390])).

tff(c_395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_20,c_16,c_307,c_393])).

tff(c_396,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_398,plain,(
    r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_396])).

tff(c_424,plain,(
    ! [D_155,C_156,A_157,B_158] :
      ( r1_tsep_1(D_155,C_156)
      | ~ r1_tsep_1(D_155,k1_tsep_1(A_157,B_158,C_156))
      | ~ m1_pre_topc(D_155,A_157)
      | v2_struct_0(D_155)
      | ~ m1_pre_topc(C_156,A_157)
      | v2_struct_0(C_156)
      | ~ m1_pre_topc(B_158,A_157)
      | v2_struct_0(B_158)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_427,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_398,c_424])).

tff(c_430,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_18,c_14,c_427])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_20,c_16,c_307,c_430])).

tff(c_433,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_396])).

tff(c_434,plain,(
    ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_396])).

tff(c_397,plain,(
    ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_74,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_435,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_397,c_74])).

tff(c_436,plain,(
    r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_435])).

tff(c_437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_436])).

tff(c_438,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_435])).

tff(c_486,plain,(
    ! [C_179,D_180,B_181,A_182] :
      ( ~ r1_tsep_1(C_179,D_180)
      | ~ r1_tsep_1(B_181,D_180)
      | r1_tsep_1(k1_tsep_1(A_182,B_181,C_179),D_180)
      | ~ m1_pre_topc(D_180,A_182)
      | v2_struct_0(D_180)
      | ~ m1_pre_topc(C_179,A_182)
      | v2_struct_0(C_179)
      | ~ m1_pre_topc(B_181,A_182)
      | v2_struct_0(B_181)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_503,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_486,c_397])).

tff(c_510,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_18,c_14,c_433,c_438,c_503])).

tff(c_512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_20,c_16,c_510])).

tff(c_514,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_513,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_516,plain,(
    r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_513])).

tff(c_92,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_2','#skF_4')
    | ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_523,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_92])).

tff(c_524,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_514,c_523])).

tff(c_525,plain,(
    ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_524])).

tff(c_532,plain,(
    ! [B_183,D_184,A_185,C_186] :
      ( r1_tsep_1(B_183,D_184)
      | ~ r1_tsep_1(k1_tsep_1(A_185,B_183,C_186),D_184)
      | ~ m1_pre_topc(D_184,A_185)
      | v2_struct_0(D_184)
      | ~ m1_pre_topc(C_186,A_185)
      | v2_struct_0(C_186)
      | ~ m1_pre_topc(B_183,A_185)
      | v2_struct_0(B_183)
      | ~ l1_pre_topc(A_185)
      | ~ v2_pre_topc(A_185)
      | v2_struct_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_535,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_516,c_532])).

tff(c_538,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_18,c_14,c_535])).

tff(c_540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_20,c_16,c_525,c_538])).

tff(c_541,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_524])).

tff(c_543,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_541])).

tff(c_560,plain,(
    ! [C_195,D_196,A_197,B_198] :
      ( r1_tsep_1(C_195,D_196)
      | ~ r1_tsep_1(k1_tsep_1(A_197,B_198,C_195),D_196)
      | ~ m1_pre_topc(D_196,A_197)
      | v2_struct_0(D_196)
      | ~ m1_pre_topc(C_195,A_197)
      | v2_struct_0(C_195)
      | ~ m1_pre_topc(B_198,A_197)
      | v2_struct_0(B_198)
      | ~ l1_pre_topc(A_197)
      | ~ v2_pre_topc(A_197)
      | v2_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_563,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_516,c_560])).

tff(c_566,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_18,c_14,c_563])).

tff(c_568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_20,c_16,c_543,c_566])).

tff(c_569,plain,(
    r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_541])).

tff(c_601,plain,(
    ! [D_211,B_212,A_213,C_214] :
      ( r1_tsep_1(D_211,B_212)
      | ~ r1_tsep_1(D_211,k1_tsep_1(A_213,B_212,C_214))
      | ~ m1_pre_topc(D_211,A_213)
      | v2_struct_0(D_211)
      | ~ m1_pre_topc(C_214,A_213)
      | v2_struct_0(C_214)
      | ~ m1_pre_topc(B_212,A_213)
      | v2_struct_0(B_212)
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_604,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_569,c_601])).

tff(c_607,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_18,c_14,c_604])).

tff(c_609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_20,c_16,c_514,c_607])).

tff(c_610,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_513])).

tff(c_612,plain,(
    r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_610])).

tff(c_638,plain,(
    ! [D_227,B_228,A_229,C_230] :
      ( r1_tsep_1(D_227,B_228)
      | ~ r1_tsep_1(D_227,k1_tsep_1(A_229,B_228,C_230))
      | ~ m1_pre_topc(D_227,A_229)
      | v2_struct_0(D_227)
      | ~ m1_pre_topc(C_230,A_229)
      | v2_struct_0(C_230)
      | ~ m1_pre_topc(B_228,A_229)
      | v2_struct_0(B_228)
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_641,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_612,c_638])).

tff(c_644,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_18,c_14,c_641])).

tff(c_646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_20,c_16,c_514,c_644])).

tff(c_648,plain,(
    ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_610])).

tff(c_611,plain,(
    ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_513])).

tff(c_102,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_651,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_514,c_648,c_611,c_102])).

tff(c_647,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_610])).

tff(c_696,plain,(
    ! [C_251,D_252,B_253,A_254] :
      ( ~ r1_tsep_1(C_251,D_252)
      | ~ r1_tsep_1(B_253,D_252)
      | r1_tsep_1(k1_tsep_1(A_254,B_253,C_251),D_252)
      | ~ m1_pre_topc(D_252,A_254)
      | v2_struct_0(D_252)
      | ~ m1_pre_topc(C_251,A_254)
      | v2_struct_0(C_251)
      | ~ m1_pre_topc(B_253,A_254)
      | v2_struct_0(B_253)
      | ~ l1_pre_topc(A_254)
      | ~ v2_pre_topc(A_254)
      | v2_struct_0(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_713,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_696,c_611])).

tff(c_720,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_22,c_18,c_14,c_651,c_647,c_713])).

tff(c_722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_20,c_16,c_720])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.41  
% 2.96/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.41  %$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tsep_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.96/1.41  
% 2.96/1.41  %Foreground sorts:
% 2.96/1.41  
% 2.96/1.41  
% 2.96/1.41  %Background operators:
% 2.96/1.41  
% 2.96/1.41  
% 2.96/1.41  %Foreground operators:
% 2.96/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.96/1.41  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 2.96/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.96/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.96/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.96/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.41  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.96/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.96/1.41  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.96/1.41  
% 2.96/1.44  tff(f_132, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((((r1_tsep_1(k1_tsep_1(A, B, C), D) => (r1_tsep_1(B, D) & r1_tsep_1(C, D))) & ((r1_tsep_1(B, D) & r1_tsep_1(C, D)) => r1_tsep_1(k1_tsep_1(A, B, C), D))) & (r1_tsep_1(D, k1_tsep_1(A, B, C)) => (r1_tsep_1(D, B) & r1_tsep_1(D, C)))) & ((r1_tsep_1(D, B) & r1_tsep_1(D, C)) => r1_tsep_1(D, k1_tsep_1(A, B, C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_tmap_1)).
% 2.96/1.44  tff(f_82, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (((~((~r1_tsep_1(k1_tsep_1(A, B, C), D) & r1_tsep_1(B, D)) & r1_tsep_1(C, D)) & ~(~(r1_tsep_1(B, D) & r1_tsep_1(C, D)) & r1_tsep_1(k1_tsep_1(A, B, C), D))) & ~((~r1_tsep_1(D, k1_tsep_1(A, B, C)) & r1_tsep_1(D, B)) & r1_tsep_1(D, C))) & ~(~(r1_tsep_1(D, B) & r1_tsep_1(D, C)) & r1_tsep_1(D, k1_tsep_1(A, B, C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_tmap_1)).
% 2.96/1.44  tff(c_30, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_24, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_20, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_16, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_22, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_18, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_14, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_98, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_103, plain, (r1_tsep_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_98])).
% 2.96/1.44  tff(c_78, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_104, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_78])).
% 2.96/1.44  tff(c_141, plain, (![D_47, C_48, B_49, A_50]: (~r1_tsep_1(D_47, C_48) | ~r1_tsep_1(D_47, B_49) | r1_tsep_1(D_47, k1_tsep_1(A_50, B_49, C_48)) | ~m1_pre_topc(D_47, A_50) | v2_struct_0(D_47) | ~m1_pre_topc(C_48, A_50) | v2_struct_0(C_48) | ~m1_pre_topc(B_49, A_50) | v2_struct_0(B_49) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.96/1.44  tff(c_38, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_3', '#skF_4') | ~r1_tsep_1('#skF_4', '#skF_3') | ~r1_tsep_1('#skF_4', '#skF_2') | ~r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_108, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_3', '#skF_4') | ~r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_104, c_38])).
% 2.96/1.44  tff(c_109, plain, (~r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_108])).
% 2.96/1.44  tff(c_158, plain, (~r1_tsep_1('#skF_4', '#skF_3') | ~r1_tsep_1('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_141, c_109])).
% 2.96/1.44  tff(c_165, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_18, c_14, c_103, c_104, c_158])).
% 2.96/1.44  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_20, c_16, c_165])).
% 2.96/1.44  tff(c_169, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_108])).
% 2.96/1.44  tff(c_168, plain, (r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_108])).
% 2.96/1.44  tff(c_170, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_168])).
% 2.96/1.44  tff(c_32, plain, (~r1_tsep_1('#skF_3', '#skF_4') | ~r1_tsep_1('#skF_2', '#skF_4') | ~r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~r1_tsep_1('#skF_4', '#skF_3') | ~r1_tsep_1('#skF_4', '#skF_2') | ~r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_177, plain, (~r1_tsep_1('#skF_3', '#skF_4') | ~r1_tsep_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_103, c_104, c_170, c_32])).
% 2.96/1.44  tff(c_178, plain, (~r1_tsep_1('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_177])).
% 2.96/1.44  tff(c_187, plain, (![B_55, D_56, A_57, C_58]: (r1_tsep_1(B_55, D_56) | ~r1_tsep_1(k1_tsep_1(A_57, B_55, C_58), D_56) | ~m1_pre_topc(D_56, A_57) | v2_struct_0(D_56) | ~m1_pre_topc(C_58, A_57) | v2_struct_0(C_58) | ~m1_pre_topc(B_55, A_57) | v2_struct_0(B_55) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.96/1.44  tff(c_190, plain, (r1_tsep_1('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_170, c_187])).
% 2.96/1.44  tff(c_193, plain, (r1_tsep_1('#skF_2', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_18, c_14, c_190])).
% 2.96/1.44  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_20, c_16, c_178, c_193])).
% 2.96/1.44  tff(c_196, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_177])).
% 2.96/1.44  tff(c_222, plain, (![C_71, D_72, A_73, B_74]: (r1_tsep_1(C_71, D_72) | ~r1_tsep_1(k1_tsep_1(A_73, B_74, C_71), D_72) | ~m1_pre_topc(D_72, A_73) | v2_struct_0(D_72) | ~m1_pre_topc(C_71, A_73) | v2_struct_0(C_71) | ~m1_pre_topc(B_74, A_73) | v2_struct_0(B_74) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.96/1.44  tff(c_225, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_170, c_222])).
% 2.96/1.44  tff(c_228, plain, (r1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_18, c_14, c_225])).
% 2.96/1.44  tff(c_230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_20, c_16, c_196, c_228])).
% 2.96/1.44  tff(c_232, plain, (~r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_168])).
% 2.96/1.44  tff(c_42, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_2', '#skF_4') | ~r1_tsep_1('#skF_4', '#skF_3') | ~r1_tsep_1('#skF_4', '#skF_2') | ~r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_236, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_103, c_104, c_42])).
% 2.96/1.44  tff(c_237, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_232, c_236])).
% 2.96/1.44  tff(c_231, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_168])).
% 2.96/1.44  tff(c_279, plain, (![C_95, D_96, B_97, A_98]: (~r1_tsep_1(C_95, D_96) | ~r1_tsep_1(B_97, D_96) | r1_tsep_1(k1_tsep_1(A_98, B_97, C_95), D_96) | ~m1_pre_topc(D_96, A_98) | v2_struct_0(D_96) | ~m1_pre_topc(C_95, A_98) | v2_struct_0(C_95) | ~m1_pre_topc(B_97, A_98) | v2_struct_0(B_97) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.96/1.44  tff(c_296, plain, (~r1_tsep_1('#skF_3', '#skF_4') | ~r1_tsep_1('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_279, c_232])).
% 2.96/1.44  tff(c_303, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_18, c_14, c_237, c_231, c_296])).
% 2.96/1.44  tff(c_305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_20, c_16, c_303])).
% 2.96/1.44  tff(c_307, plain, (~r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_78])).
% 2.96/1.44  tff(c_306, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_78])).
% 2.96/1.44  tff(c_308, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_306])).
% 2.96/1.44  tff(c_68, plain, (~r1_tsep_1('#skF_3', '#skF_4') | ~r1_tsep_1('#skF_2', '#skF_4') | ~r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_319, plain, (~r1_tsep_1('#skF_3', '#skF_4') | ~r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_308, c_68])).
% 2.96/1.44  tff(c_320, plain, (~r1_tsep_1('#skF_3', '#skF_4') | ~r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_307, c_319])).
% 2.96/1.44  tff(c_321, plain, (~r1_tsep_1('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_320])).
% 2.96/1.44  tff(c_334, plain, (![B_111, D_112, A_113, C_114]: (r1_tsep_1(B_111, D_112) | ~r1_tsep_1(k1_tsep_1(A_113, B_111, C_114), D_112) | ~m1_pre_topc(D_112, A_113) | v2_struct_0(D_112) | ~m1_pre_topc(C_114, A_113) | v2_struct_0(C_114) | ~m1_pre_topc(B_111, A_113) | v2_struct_0(B_111) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.96/1.44  tff(c_337, plain, (r1_tsep_1('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_308, c_334])).
% 2.96/1.44  tff(c_340, plain, (r1_tsep_1('#skF_2', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_18, c_14, c_337])).
% 2.96/1.44  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_20, c_16, c_321, c_340])).
% 2.96/1.44  tff(c_343, plain, (~r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_320])).
% 2.96/1.44  tff(c_345, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_343])).
% 2.96/1.44  tff(c_358, plain, (![C_127, D_128, A_129, B_130]: (r1_tsep_1(C_127, D_128) | ~r1_tsep_1(k1_tsep_1(A_129, B_130, C_127), D_128) | ~m1_pre_topc(D_128, A_129) | v2_struct_0(D_128) | ~m1_pre_topc(C_127, A_129) | v2_struct_0(C_127) | ~m1_pre_topc(B_130, A_129) | v2_struct_0(B_130) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.96/1.44  tff(c_361, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_308, c_358])).
% 2.96/1.44  tff(c_364, plain, (r1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_18, c_14, c_361])).
% 2.96/1.44  tff(c_366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_20, c_16, c_345, c_364])).
% 2.96/1.44  tff(c_367, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_343])).
% 2.96/1.44  tff(c_387, plain, (![D_139, C_140, A_141, B_142]: (r1_tsep_1(D_139, C_140) | ~r1_tsep_1(D_139, k1_tsep_1(A_141, B_142, C_140)) | ~m1_pre_topc(D_139, A_141) | v2_struct_0(D_139) | ~m1_pre_topc(C_140, A_141) | v2_struct_0(C_140) | ~m1_pre_topc(B_142, A_141) | v2_struct_0(B_142) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.96/1.44  tff(c_390, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_367, c_387])).
% 2.96/1.44  tff(c_393, plain, (r1_tsep_1('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_18, c_14, c_390])).
% 2.96/1.44  tff(c_395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_20, c_16, c_307, c_393])).
% 2.96/1.44  tff(c_396, plain, (r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_306])).
% 2.96/1.44  tff(c_398, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_396])).
% 2.96/1.44  tff(c_424, plain, (![D_155, C_156, A_157, B_158]: (r1_tsep_1(D_155, C_156) | ~r1_tsep_1(D_155, k1_tsep_1(A_157, B_158, C_156)) | ~m1_pre_topc(D_155, A_157) | v2_struct_0(D_155) | ~m1_pre_topc(C_156, A_157) | v2_struct_0(C_156) | ~m1_pre_topc(B_158, A_157) | v2_struct_0(B_158) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.96/1.44  tff(c_427, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_398, c_424])).
% 2.96/1.44  tff(c_430, plain, (r1_tsep_1('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_18, c_14, c_427])).
% 2.96/1.44  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_20, c_16, c_307, c_430])).
% 2.96/1.44  tff(c_433, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_396])).
% 2.96/1.44  tff(c_434, plain, (~r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_396])).
% 2.96/1.44  tff(c_397, plain, (~r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_306])).
% 2.96/1.44  tff(c_74, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_435, plain, (r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_307, c_397, c_74])).
% 2.96/1.44  tff(c_436, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_435])).
% 2.96/1.44  tff(c_437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_434, c_436])).
% 2.96/1.44  tff(c_438, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_435])).
% 2.96/1.44  tff(c_486, plain, (![C_179, D_180, B_181, A_182]: (~r1_tsep_1(C_179, D_180) | ~r1_tsep_1(B_181, D_180) | r1_tsep_1(k1_tsep_1(A_182, B_181, C_179), D_180) | ~m1_pre_topc(D_180, A_182) | v2_struct_0(D_180) | ~m1_pre_topc(C_179, A_182) | v2_struct_0(C_179) | ~m1_pre_topc(B_181, A_182) | v2_struct_0(B_181) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.96/1.44  tff(c_503, plain, (~r1_tsep_1('#skF_3', '#skF_4') | ~r1_tsep_1('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_486, c_397])).
% 2.96/1.44  tff(c_510, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_18, c_14, c_433, c_438, c_503])).
% 2.96/1.44  tff(c_512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_20, c_16, c_510])).
% 2.96/1.44  tff(c_514, plain, (~r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_98])).
% 2.96/1.44  tff(c_513, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_98])).
% 2.96/1.44  tff(c_516, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_513])).
% 2.96/1.44  tff(c_92, plain, (~r1_tsep_1('#skF_3', '#skF_4') | ~r1_tsep_1('#skF_2', '#skF_4') | ~r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_523, plain, (~r1_tsep_1('#skF_3', '#skF_4') | ~r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_516, c_92])).
% 2.96/1.44  tff(c_524, plain, (~r1_tsep_1('#skF_3', '#skF_4') | ~r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_514, c_523])).
% 2.96/1.44  tff(c_525, plain, (~r1_tsep_1('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_524])).
% 2.96/1.44  tff(c_532, plain, (![B_183, D_184, A_185, C_186]: (r1_tsep_1(B_183, D_184) | ~r1_tsep_1(k1_tsep_1(A_185, B_183, C_186), D_184) | ~m1_pre_topc(D_184, A_185) | v2_struct_0(D_184) | ~m1_pre_topc(C_186, A_185) | v2_struct_0(C_186) | ~m1_pre_topc(B_183, A_185) | v2_struct_0(B_183) | ~l1_pre_topc(A_185) | ~v2_pre_topc(A_185) | v2_struct_0(A_185))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.96/1.44  tff(c_535, plain, (r1_tsep_1('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_516, c_532])).
% 2.96/1.44  tff(c_538, plain, (r1_tsep_1('#skF_2', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_18, c_14, c_535])).
% 2.96/1.44  tff(c_540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_20, c_16, c_525, c_538])).
% 2.96/1.44  tff(c_541, plain, (~r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_524])).
% 2.96/1.44  tff(c_543, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_541])).
% 2.96/1.44  tff(c_560, plain, (![C_195, D_196, A_197, B_198]: (r1_tsep_1(C_195, D_196) | ~r1_tsep_1(k1_tsep_1(A_197, B_198, C_195), D_196) | ~m1_pre_topc(D_196, A_197) | v2_struct_0(D_196) | ~m1_pre_topc(C_195, A_197) | v2_struct_0(C_195) | ~m1_pre_topc(B_198, A_197) | v2_struct_0(B_198) | ~l1_pre_topc(A_197) | ~v2_pre_topc(A_197) | v2_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.96/1.44  tff(c_563, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_516, c_560])).
% 2.96/1.44  tff(c_566, plain, (r1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_18, c_14, c_563])).
% 2.96/1.44  tff(c_568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_20, c_16, c_543, c_566])).
% 2.96/1.44  tff(c_569, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_541])).
% 2.96/1.44  tff(c_601, plain, (![D_211, B_212, A_213, C_214]: (r1_tsep_1(D_211, B_212) | ~r1_tsep_1(D_211, k1_tsep_1(A_213, B_212, C_214)) | ~m1_pre_topc(D_211, A_213) | v2_struct_0(D_211) | ~m1_pre_topc(C_214, A_213) | v2_struct_0(C_214) | ~m1_pre_topc(B_212, A_213) | v2_struct_0(B_212) | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213) | v2_struct_0(A_213))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.96/1.44  tff(c_604, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_569, c_601])).
% 2.96/1.44  tff(c_607, plain, (r1_tsep_1('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_18, c_14, c_604])).
% 2.96/1.44  tff(c_609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_20, c_16, c_514, c_607])).
% 2.96/1.44  tff(c_610, plain, (r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_513])).
% 2.96/1.44  tff(c_612, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_610])).
% 2.96/1.44  tff(c_638, plain, (![D_227, B_228, A_229, C_230]: (r1_tsep_1(D_227, B_228) | ~r1_tsep_1(D_227, k1_tsep_1(A_229, B_228, C_230)) | ~m1_pre_topc(D_227, A_229) | v2_struct_0(D_227) | ~m1_pre_topc(C_230, A_229) | v2_struct_0(C_230) | ~m1_pre_topc(B_228, A_229) | v2_struct_0(B_228) | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.96/1.44  tff(c_641, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_612, c_638])).
% 2.96/1.44  tff(c_644, plain, (r1_tsep_1('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_18, c_14, c_641])).
% 2.96/1.44  tff(c_646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_20, c_16, c_514, c_644])).
% 2.96/1.44  tff(c_648, plain, (~r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_610])).
% 2.96/1.44  tff(c_611, plain, (~r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_513])).
% 2.96/1.44  tff(c_102, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.96/1.44  tff(c_651, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_514, c_648, c_611, c_102])).
% 2.96/1.44  tff(c_647, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_610])).
% 2.96/1.44  tff(c_696, plain, (![C_251, D_252, B_253, A_254]: (~r1_tsep_1(C_251, D_252) | ~r1_tsep_1(B_253, D_252) | r1_tsep_1(k1_tsep_1(A_254, B_253, C_251), D_252) | ~m1_pre_topc(D_252, A_254) | v2_struct_0(D_252) | ~m1_pre_topc(C_251, A_254) | v2_struct_0(C_251) | ~m1_pre_topc(B_253, A_254) | v2_struct_0(B_253) | ~l1_pre_topc(A_254) | ~v2_pre_topc(A_254) | v2_struct_0(A_254))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.96/1.44  tff(c_713, plain, (~r1_tsep_1('#skF_3', '#skF_4') | ~r1_tsep_1('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_696, c_611])).
% 2.96/1.44  tff(c_720, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_22, c_18, c_14, c_651, c_647, c_713])).
% 2.96/1.44  tff(c_722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_20, c_16, c_720])).
% 2.96/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.44  
% 2.96/1.44  Inference rules
% 2.96/1.44  ----------------------
% 2.96/1.44  #Ref     : 0
% 2.96/1.44  #Sup     : 64
% 2.96/1.44  #Fact    : 0
% 2.96/1.44  #Define  : 0
% 2.96/1.44  #Split   : 15
% 2.96/1.44  #Chain   : 0
% 2.96/1.44  #Close   : 0
% 2.96/1.44  
% 2.96/1.44  Ordering : KBO
% 2.96/1.44  
% 2.96/1.44  Simplification rules
% 2.96/1.44  ----------------------
% 2.96/1.44  #Subsume      : 42
% 2.96/1.44  #Demod        : 327
% 2.96/1.44  #Tautology    : 77
% 2.96/1.44  #SimpNegUnit  : 63
% 2.96/1.44  #BackRed      : 0
% 2.96/1.44  
% 2.96/1.44  #Partial instantiations: 0
% 2.96/1.44  #Strategies tried      : 1
% 2.96/1.44  
% 2.96/1.44  Timing (in seconds)
% 2.96/1.44  ----------------------
% 2.96/1.44  Preprocessing        : 0.30
% 2.96/1.44  Parsing              : 0.16
% 2.96/1.44  CNF conversion       : 0.03
% 2.96/1.44  Main loop            : 0.36
% 2.96/1.44  Inferencing          : 0.13
% 2.96/1.44  Reduction            : 0.10
% 2.96/1.44  Demodulation         : 0.06
% 2.96/1.44  BG Simplification    : 0.02
% 2.96/1.44  Subsumption          : 0.09
% 2.96/1.44  Abstraction          : 0.02
% 2.96/1.44  MUC search           : 0.00
% 2.96/1.44  Cooper               : 0.00
% 2.96/1.44  Total                : 0.71
% 2.96/1.44  Index Insertion      : 0.00
% 2.96/1.44  Index Deletion       : 0.00
% 2.96/1.44  Index Matching       : 0.00
% 2.96/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
