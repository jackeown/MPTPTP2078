%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:44 EST 2020

% Result     : Theorem 14.80s
% Output     : CNFRefutation 14.99s
% Verified   : 
% Statistics : Number of formulae       :  177 (7187 expanded)
%              Number of leaves         :   23 (2650 expanded)
%              Depth                    :   53
%              Number of atoms          :  794 (50484 expanded)
%              Number of equality atoms :   45 (2566 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_181,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_147,axiom,(
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
               => ( ( m1_pre_topc(B,C)
                   => k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) )
                  & ( k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                   => m1_pre_topc(B,C) )
                  & ( m1_pre_topc(C,B)
                   => k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) )
                  & ( k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                   => m1_pre_topc(C,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tsep_1)).

tff(f_66,axiom,(
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
             => ( m1_pre_topc(B,C)
               => ( ~ r1_tsep_1(B,C)
                  & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_105,axiom,(
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
                 => ! [E] :
                      ( ( ~ v2_struct_0(E)
                        & m1_pre_topc(E,A) )
                     => ( ( m1_pre_topc(B,D)
                          & m1_pre_topc(C,E) )
                       => ( r1_tsep_1(B,C)
                          | m1_pre_topc(k2_tsep_1(A,B,C),k2_tsep_1(A,D,E)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tmap_1)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_24,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_38,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_48,plain,(
    ! [B_65,A_66] :
      ( l1_pre_topc(B_65)
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_48])).

tff(c_72,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_60])).

tff(c_12,plain,(
    ! [A_45] :
      ( m1_pre_topc(A_45,A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2848,plain,(
    ! [A_160,B_161,C_162] :
      ( k2_tsep_1(A_160,B_161,C_162) = g1_pre_topc(u1_struct_0(B_161),u1_pre_topc(B_161))
      | ~ m1_pre_topc(B_161,C_162)
      | r1_tsep_1(B_161,C_162)
      | ~ m1_pre_topc(C_162,A_160)
      | v2_struct_0(C_162)
      | ~ m1_pre_topc(B_161,A_160)
      | v2_struct_0(B_161)
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2866,plain,(
    ! [B_161] :
      ( g1_pre_topc(u1_struct_0(B_161),u1_pre_topc(B_161)) = k2_tsep_1('#skF_1',B_161,'#skF_4')
      | ~ m1_pre_topc(B_161,'#skF_4')
      | r1_tsep_1(B_161,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_161,'#skF_1')
      | v2_struct_0(B_161)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_2848])).

tff(c_2899,plain,(
    ! [B_161] :
      ( g1_pre_topc(u1_struct_0(B_161),u1_pre_topc(B_161)) = k2_tsep_1('#skF_1',B_161,'#skF_4')
      | ~ m1_pre_topc(B_161,'#skF_4')
      | r1_tsep_1(B_161,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_161,'#skF_1')
      | v2_struct_0(B_161)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_2866])).

tff(c_2900,plain,(
    ! [B_161] :
      ( g1_pre_topc(u1_struct_0(B_161),u1_pre_topc(B_161)) = k2_tsep_1('#skF_1',B_161,'#skF_4')
      | ~ m1_pre_topc(B_161,'#skF_4')
      | r1_tsep_1(B_161,'#skF_4')
      | ~ m1_pre_topc(B_161,'#skF_1')
      | v2_struct_0(B_161) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_32,c_2899])).

tff(c_101,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_tsep_1(A_76,B_77,C_78) = g1_pre_topc(u1_struct_0(C_78),u1_pre_topc(C_78))
      | ~ m1_pre_topc(C_78,B_77)
      | r1_tsep_1(B_77,C_78)
      | ~ m1_pre_topc(C_78,A_76)
      | v2_struct_0(C_78)
      | ~ m1_pre_topc(B_77,A_76)
      | v2_struct_0(B_77)
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_111,plain,(
    ! [B_77] :
      ( k2_tsep_1('#skF_1',B_77,'#skF_4') = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ m1_pre_topc('#skF_4',B_77)
      | r1_tsep_1(B_77,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_101])).

tff(c_128,plain,(
    ! [B_77] :
      ( k2_tsep_1('#skF_1',B_77,'#skF_4') = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ m1_pre_topc('#skF_4',B_77)
      | r1_tsep_1(B_77,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_111])).

tff(c_129,plain,(
    ! [B_77] :
      ( k2_tsep_1('#skF_1',B_77,'#skF_4') = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ m1_pre_topc('#skF_4',B_77)
      | r1_tsep_1(B_77,'#skF_4')
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_32,c_128])).

tff(c_115,plain,(
    ! [B_77] :
      ( k2_tsep_1('#skF_1',B_77,'#skF_3') = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc('#skF_3',B_77)
      | r1_tsep_1(B_77,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_101])).

tff(c_136,plain,(
    ! [B_77] :
      ( k2_tsep_1('#skF_1',B_77,'#skF_3') = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc('#skF_3',B_77)
      | r1_tsep_1(B_77,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_115])).

tff(c_173,plain,(
    ! [B_83] :
      ( k2_tsep_1('#skF_1',B_83,'#skF_3') = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc('#skF_3',B_83)
      | r1_tsep_1(B_83,'#skF_3')
      | ~ m1_pre_topc(B_83,'#skF_1')
      | v2_struct_0(B_83) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_36,c_136])).

tff(c_6,plain,(
    ! [C_13,B_11,A_7] :
      ( ~ r1_tsep_1(C_13,B_11)
      | ~ m1_pre_topc(B_11,C_13)
      | ~ m1_pre_topc(C_13,A_7)
      | v2_struct_0(C_13)
      | ~ m1_pre_topc(B_11,A_7)
      | v2_struct_0(B_11)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_189,plain,(
    ! [B_83,A_7] :
      ( ~ m1_pre_topc(B_83,A_7)
      | ~ m1_pre_topc('#skF_3',A_7)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7)
      | k2_tsep_1('#skF_1',B_83,'#skF_3') = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc('#skF_3',B_83)
      | ~ m1_pre_topc(B_83,'#skF_1')
      | v2_struct_0(B_83) ) ),
    inference(resolution,[status(thm)],[c_173,c_6])).

tff(c_361,plain,(
    ! [B_97,A_98] :
      ( ~ m1_pre_topc(B_97,A_98)
      | ~ m1_pre_topc('#skF_3',A_98)
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98)
      | k2_tsep_1('#skF_1',B_97,'#skF_3') = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc('#skF_3',B_97)
      | ~ m1_pre_topc(B_97,'#skF_1')
      | v2_struct_0(B_97) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_189])).

tff(c_377,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k2_tsep_1('#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_361])).

tff(c_406,plain,
    ( v2_struct_0('#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k2_tsep_1('#skF_1','#skF_4','#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_44,c_42,c_34,c_377])).

tff(c_407,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k2_tsep_1('#skF_1','#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_46,c_406])).

tff(c_395,plain,(
    ! [A_45] :
      ( ~ v2_pre_topc(A_45)
      | k2_tsep_1('#skF_1',A_45,'#skF_3') = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_45)
      | ~ m1_pre_topc(A_45,'#skF_1')
      | v2_struct_0(A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_12,c_361])).

tff(c_3633,plain,(
    ! [A_180] :
      ( ~ v2_pre_topc(A_180)
      | k2_tsep_1('#skF_1',A_180,'#skF_3') = k2_tsep_1('#skF_1','#skF_4','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_180)
      | ~ m1_pre_topc(A_180,'#skF_1')
      | v2_struct_0(A_180)
      | ~ l1_pre_topc(A_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_395])).

tff(c_3642,plain,
    ( ~ v2_pre_topc('#skF_1')
    | k2_tsep_1('#skF_1','#skF_1','#skF_3') = k2_tsep_1('#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_3633])).

tff(c_3657,plain,
    ( k2_tsep_1('#skF_1','#skF_1','#skF_3') = k2_tsep_1('#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_3642])).

tff(c_3658,plain,
    ( k2_tsep_1('#skF_1','#skF_1','#skF_3') = k2_tsep_1('#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3657])).

tff(c_3659,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3658])).

tff(c_3662,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_3659])).

tff(c_3666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3662])).

tff(c_3668,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_3658])).

tff(c_20,plain,(
    ! [A_46,B_50,C_52] :
      ( k2_tsep_1(A_46,B_50,C_52) = g1_pre_topc(u1_struct_0(B_50),u1_pre_topc(B_50))
      | ~ m1_pre_topc(B_50,C_52)
      | r1_tsep_1(B_50,C_52)
      | ~ m1_pre_topc(C_52,A_46)
      | v2_struct_0(C_52)
      | ~ m1_pre_topc(B_50,A_46)
      | v2_struct_0(B_50)
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_3670,plain,(
    ! [B_50] :
      ( g1_pre_topc(u1_struct_0(B_50),u1_pre_topc(B_50)) = k2_tsep_1('#skF_1',B_50,'#skF_1')
      | r1_tsep_1(B_50,'#skF_1')
      | ~ m1_pre_topc(B_50,'#skF_1')
      | v2_struct_0(B_50)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3668,c_20])).

tff(c_3678,plain,(
    ! [B_50] :
      ( g1_pre_topc(u1_struct_0(B_50),u1_pre_topc(B_50)) = k2_tsep_1('#skF_1',B_50,'#skF_1')
      | r1_tsep_1(B_50,'#skF_1')
      | ~ m1_pre_topc(B_50,'#skF_1')
      | v2_struct_0(B_50)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3670])).

tff(c_3679,plain,(
    ! [B_50] :
      ( g1_pre_topc(u1_struct_0(B_50),u1_pre_topc(B_50)) = k2_tsep_1('#skF_1',B_50,'#skF_1')
      | r1_tsep_1(B_50,'#skF_1')
      | ~ m1_pre_topc(B_50,'#skF_1')
      | v2_struct_0(B_50) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3678])).

tff(c_117,plain,(
    ! [A_45,B_77] :
      ( k2_tsep_1(A_45,B_77,A_45) = g1_pre_topc(u1_struct_0(A_45),u1_pre_topc(A_45))
      | ~ m1_pre_topc(A_45,B_77)
      | r1_tsep_1(B_77,A_45)
      | ~ m1_pre_topc(B_77,A_45)
      | v2_struct_0(B_77)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_12,c_101])).

tff(c_16,plain,(
    ! [A_46,B_50,C_52] :
      ( k2_tsep_1(A_46,B_50,C_52) = g1_pre_topc(u1_struct_0(C_52),u1_pre_topc(C_52))
      | ~ m1_pre_topc(C_52,B_50)
      | r1_tsep_1(B_50,C_52)
      | ~ m1_pre_topc(C_52,A_46)
      | v2_struct_0(C_52)
      | ~ m1_pre_topc(B_50,A_46)
      | v2_struct_0(B_50)
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_3672,plain,(
    ! [B_50] :
      ( k2_tsep_1('#skF_1',B_50,'#skF_1') = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ m1_pre_topc('#skF_1',B_50)
      | r1_tsep_1(B_50,'#skF_1')
      | ~ m1_pre_topc(B_50,'#skF_1')
      | v2_struct_0(B_50)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_3668,c_16])).

tff(c_3682,plain,(
    ! [B_50] :
      ( k2_tsep_1('#skF_1',B_50,'#skF_1') = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ m1_pre_topc('#skF_1',B_50)
      | r1_tsep_1(B_50,'#skF_1')
      | ~ m1_pre_topc(B_50,'#skF_1')
      | v2_struct_0(B_50)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3672])).

tff(c_3973,plain,(
    ! [B_190] :
      ( k2_tsep_1('#skF_1',B_190,'#skF_1') = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ m1_pre_topc('#skF_1',B_190)
      | r1_tsep_1(B_190,'#skF_1')
      | ~ m1_pre_topc(B_190,'#skF_1')
      | v2_struct_0(B_190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3682])).

tff(c_4,plain,(
    ! [B_6,A_4] :
      ( m1_pre_topc(B_6,A_4)
      | ~ m1_pre_topc(B_6,g1_pre_topc(u1_struct_0(A_4),u1_pre_topc(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4019,plain,(
    ! [B_6,B_190] :
      ( m1_pre_topc(B_6,'#skF_1')
      | ~ m1_pre_topc(B_6,k2_tsep_1('#skF_1',B_190,'#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc('#skF_1',B_190)
      | r1_tsep_1(B_190,'#skF_1')
      | ~ m1_pre_topc(B_190,'#skF_1')
      | v2_struct_0(B_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3973,c_4])).

tff(c_4115,plain,(
    ! [B_191,B_192] :
      ( m1_pre_topc(B_191,'#skF_1')
      | ~ m1_pre_topc(B_191,k2_tsep_1('#skF_1',B_192,'#skF_1'))
      | ~ m1_pre_topc('#skF_1',B_192)
      | r1_tsep_1(B_192,'#skF_1')
      | ~ m1_pre_topc(B_192,'#skF_1')
      | v2_struct_0(B_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4019])).

tff(c_4125,plain,(
    ! [B_191,B_77] :
      ( m1_pre_topc(B_191,'#skF_1')
      | ~ m1_pre_topc(B_191,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc('#skF_1',B_77)
      | r1_tsep_1(B_77,'#skF_1')
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77)
      | ~ m1_pre_topc('#skF_1',B_77)
      | r1_tsep_1(B_77,'#skF_1')
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77)
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_4115])).

tff(c_4144,plain,(
    ! [B_191,B_77] :
      ( m1_pre_topc(B_191,'#skF_1')
      | ~ m1_pre_topc(B_191,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc('#skF_1',B_77)
      | r1_tsep_1(B_77,'#skF_1')
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_4125])).

tff(c_4145,plain,(
    ! [B_191,B_77] :
      ( m1_pre_topc(B_191,'#skF_1')
      | ~ m1_pre_topc(B_191,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc('#skF_1',B_77)
      | r1_tsep_1(B_77,'#skF_1')
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4144])).

tff(c_4313,plain,(
    ! [B_202] :
      ( ~ m1_pre_topc('#skF_1',B_202)
      | r1_tsep_1(B_202,'#skF_1')
      | ~ m1_pre_topc(B_202,'#skF_1')
      | v2_struct_0(B_202) ) ),
    inference(splitLeft,[status(thm)],[c_4145])).

tff(c_8,plain,(
    ! [B_11,C_13,A_7] :
      ( ~ r1_tsep_1(B_11,C_13)
      | ~ m1_pre_topc(B_11,C_13)
      | ~ m1_pre_topc(C_13,A_7)
      | v2_struct_0(C_13)
      | ~ m1_pre_topc(B_11,A_7)
      | v2_struct_0(B_11)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4318,plain,(
    ! [A_7,B_202] :
      ( ~ m1_pre_topc('#skF_1',A_7)
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(B_202,A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7)
      | ~ m1_pre_topc('#skF_1',B_202)
      | ~ m1_pre_topc(B_202,'#skF_1')
      | v2_struct_0(B_202) ) ),
    inference(resolution,[status(thm)],[c_4313,c_8])).

tff(c_4569,plain,(
    ! [A_209,B_210] :
      ( ~ m1_pre_topc('#skF_1',A_209)
      | ~ m1_pre_topc(B_210,A_209)
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209)
      | v2_struct_0(A_209)
      | ~ m1_pre_topc('#skF_1',B_210)
      | ~ m1_pre_topc(B_210,'#skF_1')
      | v2_struct_0(B_210) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4318])).

tff(c_4571,plain,(
    ! [B_210] :
      ( ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc('#skF_1',B_210)
      | ~ m1_pre_topc(B_210,'#skF_1')
      | v2_struct_0(B_210) ) ),
    inference(resolution,[status(thm)],[c_3668,c_4569])).

tff(c_4577,plain,(
    ! [B_210] :
      ( v2_struct_0('#skF_1')
      | ~ m1_pre_topc('#skF_1',B_210)
      | ~ m1_pre_topc(B_210,'#skF_1')
      | v2_struct_0(B_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_4571])).

tff(c_4583,plain,(
    ! [B_211] :
      ( ~ m1_pre_topc('#skF_1',B_211)
      | ~ m1_pre_topc(B_211,'#skF_1')
      | v2_struct_0(B_211) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4577])).

tff(c_4585,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3668,c_4583])).

tff(c_4591,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3668,c_4585])).

tff(c_4593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4591])).

tff(c_4595,plain,(
    ! [B_212] :
      ( m1_pre_topc(B_212,'#skF_1')
      | ~ m1_pre_topc(B_212,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_4145])).

tff(c_4599,plain,(
    ! [B_212] :
      ( m1_pre_topc(B_212,'#skF_1')
      | ~ m1_pre_topc(B_212,k2_tsep_1('#skF_1','#skF_1','#skF_1'))
      | r1_tsep_1('#skF_1','#skF_1')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3679,c_4595])).

tff(c_4624,plain,(
    ! [B_212] :
      ( m1_pre_topc(B_212,'#skF_1')
      | ~ m1_pre_topc(B_212,k2_tsep_1('#skF_1','#skF_1','#skF_1'))
      | r1_tsep_1('#skF_1','#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3668,c_4599])).

tff(c_4625,plain,(
    ! [B_212] :
      ( m1_pre_topc(B_212,'#skF_1')
      | ~ m1_pre_topc(B_212,k2_tsep_1('#skF_1','#skF_1','#skF_1'))
      | r1_tsep_1('#skF_1','#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4624])).

tff(c_4641,plain,(
    r1_tsep_1('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4625])).

tff(c_4643,plain,(
    ! [A_7] :
      ( ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ m1_pre_topc('#skF_1',A_7)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(resolution,[status(thm)],[c_4641,c_8])).

tff(c_4648,plain,(
    ! [A_7] :
      ( ~ m1_pre_topc('#skF_1',A_7)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3668,c_4643])).

tff(c_4654,plain,(
    ! [A_213] :
      ( ~ m1_pre_topc('#skF_1',A_213)
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4648])).

tff(c_4657,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3668,c_4654])).

tff(c_4664,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_4657])).

tff(c_4666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4664])).

tff(c_4668,plain,(
    ~ r1_tsep_1('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_4625])).

tff(c_4672,plain,(
    ! [B_214] :
      ( m1_pre_topc(B_214,'#skF_1')
      | ~ m1_pre_topc(B_214,k2_tsep_1('#skF_1','#skF_1','#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_4625])).

tff(c_4690,plain,
    ( m1_pre_topc(k2_tsep_1('#skF_1','#skF_1','#skF_1'),'#skF_1')
    | ~ l1_pre_topc(k2_tsep_1('#skF_1','#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_4672])).

tff(c_4691,plain,(
    ~ l1_pre_topc(k2_tsep_1('#skF_1','#skF_1','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4690])).

tff(c_10,plain,(
    ! [E_44,D_42,C_38,A_14,B_30] :
      ( m1_pre_topc(k2_tsep_1(A_14,B_30,C_38),k2_tsep_1(A_14,D_42,E_44))
      | r1_tsep_1(B_30,C_38)
      | ~ m1_pre_topc(C_38,E_44)
      | ~ m1_pre_topc(B_30,D_42)
      | ~ m1_pre_topc(E_44,A_14)
      | v2_struct_0(E_44)
      | ~ m1_pre_topc(D_42,A_14)
      | v2_struct_0(D_42)
      | ~ m1_pre_topc(C_38,A_14)
      | v2_struct_0(C_38)
      | ~ m1_pre_topc(B_30,A_14)
      | v2_struct_0(B_30)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4676,plain,(
    ! [B_30,C_38] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_30,C_38),'#skF_1')
      | r1_tsep_1(B_30,C_38)
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ m1_pre_topc(C_38,'#skF_1')
      | v2_struct_0(C_38)
      | ~ m1_pre_topc(B_30,'#skF_1')
      | v2_struct_0(B_30)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10,c_4672])).

tff(c_4687,plain,(
    ! [B_30,C_38] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_30,C_38),'#skF_1')
      | r1_tsep_1(B_30,C_38)
      | ~ m1_pre_topc(C_38,'#skF_1')
      | v2_struct_0(C_38)
      | ~ m1_pre_topc(B_30,'#skF_1')
      | v2_struct_0(B_30)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3668,c_4676])).

tff(c_5419,plain,(
    ! [B_229,C_230] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_229,C_230),'#skF_1')
      | r1_tsep_1(B_229,C_230)
      | ~ m1_pre_topc(C_230,'#skF_1')
      | v2_struct_0(C_230)
      | ~ m1_pre_topc(B_229,'#skF_1')
      | v2_struct_0(B_229) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4687])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( l1_pre_topc(B_3)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5426,plain,(
    ! [B_229,C_230] :
      ( l1_pre_topc(k2_tsep_1('#skF_1',B_229,C_230))
      | ~ l1_pre_topc('#skF_1')
      | r1_tsep_1(B_229,C_230)
      | ~ m1_pre_topc(C_230,'#skF_1')
      | v2_struct_0(C_230)
      | ~ m1_pre_topc(B_229,'#skF_1')
      | v2_struct_0(B_229) ) ),
    inference(resolution,[status(thm)],[c_5419,c_2])).

tff(c_5517,plain,(
    ! [B_231,C_232] :
      ( l1_pre_topc(k2_tsep_1('#skF_1',B_231,C_232))
      | r1_tsep_1(B_231,C_232)
      | ~ m1_pre_topc(C_232,'#skF_1')
      | v2_struct_0(C_232)
      | ~ m1_pre_topc(B_231,'#skF_1')
      | v2_struct_0(B_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5426])).

tff(c_2888,plain,(
    ! [A_45,B_161] :
      ( k2_tsep_1(A_45,B_161,A_45) = g1_pre_topc(u1_struct_0(B_161),u1_pre_topc(B_161))
      | r1_tsep_1(B_161,A_45)
      | ~ m1_pre_topc(B_161,A_45)
      | v2_struct_0(B_161)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_12,c_2848])).

tff(c_4640,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_1')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_12,c_4595])).

tff(c_4949,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4640])).

tff(c_4959,plain,(
    ! [A_45] :
      ( ~ l1_pre_topc(k2_tsep_1(A_45,'#skF_1',A_45))
      | r1_tsep_1('#skF_1',A_45)
      | ~ m1_pre_topc('#skF_1',A_45)
      | v2_struct_0('#skF_1')
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2888,c_4949])).

tff(c_4975,plain,(
    ! [A_45] :
      ( ~ l1_pre_topc(k2_tsep_1(A_45,'#skF_1',A_45))
      | r1_tsep_1('#skF_1',A_45)
      | ~ m1_pre_topc('#skF_1',A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4959])).

tff(c_5521,plain,
    ( ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | r1_tsep_1('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_5517,c_4975])).

tff(c_5563,plain,
    ( r1_tsep_1('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3668,c_42,c_44,c_5521])).

tff(c_5565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4668,c_5563])).

tff(c_5567,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_4640])).

tff(c_5949,plain,
    ( l1_pre_topc(k2_tsep_1('#skF_1','#skF_1','#skF_1'))
    | r1_tsep_1('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3679,c_5567])).

tff(c_5966,plain,
    ( l1_pre_topc(k2_tsep_1('#skF_1','#skF_1','#skF_1'))
    | r1_tsep_1('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3668,c_5949])).

tff(c_5968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4668,c_4691,c_5966])).

tff(c_5970,plain,(
    l1_pre_topc(k2_tsep_1('#skF_1','#skF_1','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4690])).

tff(c_2977,plain,(
    ! [D_166,E_164,C_167,B_165,A_168] :
      ( m1_pre_topc(k2_tsep_1(A_168,B_165,C_167),k2_tsep_1(A_168,D_166,E_164))
      | r1_tsep_1(B_165,C_167)
      | ~ m1_pre_topc(C_167,E_164)
      | ~ m1_pre_topc(B_165,D_166)
      | ~ m1_pre_topc(E_164,A_168)
      | v2_struct_0(E_164)
      | ~ m1_pre_topc(D_166,A_168)
      | v2_struct_0(D_166)
      | ~ m1_pre_topc(C_167,A_168)
      | v2_struct_0(C_167)
      | ~ m1_pre_topc(B_165,A_168)
      | v2_struct_0(B_165)
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3037,plain,(
    ! [D_166,E_164,C_167,B_165,A_168] :
      ( l1_pre_topc(k2_tsep_1(A_168,B_165,C_167))
      | ~ l1_pre_topc(k2_tsep_1(A_168,D_166,E_164))
      | r1_tsep_1(B_165,C_167)
      | ~ m1_pre_topc(C_167,E_164)
      | ~ m1_pre_topc(B_165,D_166)
      | ~ m1_pre_topc(E_164,A_168)
      | v2_struct_0(E_164)
      | ~ m1_pre_topc(D_166,A_168)
      | v2_struct_0(D_166)
      | ~ m1_pre_topc(C_167,A_168)
      | v2_struct_0(C_167)
      | ~ m1_pre_topc(B_165,A_168)
      | v2_struct_0(B_165)
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_2977,c_2])).

tff(c_5972,plain,(
    ! [B_165,C_167] :
      ( l1_pre_topc(k2_tsep_1('#skF_1',B_165,C_167))
      | r1_tsep_1(B_165,C_167)
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ m1_pre_topc(C_167,'#skF_1')
      | v2_struct_0(C_167)
      | ~ m1_pre_topc(B_165,'#skF_1')
      | v2_struct_0(B_165)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_5970,c_3037])).

tff(c_5975,plain,(
    ! [B_165,C_167] :
      ( l1_pre_topc(k2_tsep_1('#skF_1',B_165,C_167))
      | r1_tsep_1(B_165,C_167)
      | ~ m1_pre_topc(C_167,'#skF_1')
      | v2_struct_0(C_167)
      | ~ m1_pre_topc(B_165,'#skF_1')
      | v2_struct_0(B_165)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3668,c_5972])).

tff(c_6852,plain,(
    ! [B_255,C_256] :
      ( l1_pre_topc(k2_tsep_1('#skF_1',B_255,C_256))
      | r1_tsep_1(B_255,C_256)
      | ~ m1_pre_topc(C_256,'#skF_1')
      | v2_struct_0(C_256)
      | ~ m1_pre_topc(B_255,'#skF_1')
      | v2_struct_0(B_255) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_5975])).

tff(c_6884,plain,(
    ! [B_77] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | r1_tsep_1(B_77,'#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77)
      | ~ m1_pre_topc('#skF_4',B_77)
      | r1_tsep_1(B_77,'#skF_4')
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_6852])).

tff(c_6914,plain,(
    ! [B_77] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_4',B_77)
      | r1_tsep_1(B_77,'#skF_4')
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6884])).

tff(c_6915,plain,(
    ! [B_77] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc('#skF_4',B_77)
      | r1_tsep_1(B_77,'#skF_4')
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6914])).

tff(c_6917,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_6915])).

tff(c_6964,plain,
    ( l1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | r1_tsep_1('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2900,c_6917])).

tff(c_6980,plain,
    ( l1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | r1_tsep_1('#skF_4','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6964])).

tff(c_6981,plain,
    ( l1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | r1_tsep_1('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6980])).

tff(c_7775,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6981])).

tff(c_7778,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_7775])).

tff(c_7782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_7778])).

tff(c_7784,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_6981])).

tff(c_7947,plain,(
    ! [B_280,C_281] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_280,C_281),'#skF_1')
      | r1_tsep_1(B_280,C_281)
      | ~ m1_pre_topc(C_281,'#skF_1')
      | v2_struct_0(C_281)
      | ~ m1_pre_topc(B_280,'#skF_1')
      | v2_struct_0(B_280) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4687])).

tff(c_7984,plain,(
    ! [B_77] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_1')
      | r1_tsep_1(B_77,'#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77)
      | ~ m1_pre_topc('#skF_4',B_77)
      | r1_tsep_1(B_77,'#skF_4')
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_7947])).

tff(c_8021,plain,(
    ! [B_77] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_4',B_77)
      | r1_tsep_1(B_77,'#skF_4')
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_7984])).

tff(c_8022,plain,(
    ! [B_77] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_1')
      | ~ m1_pre_topc('#skF_4',B_77)
      | r1_tsep_1(B_77,'#skF_4')
      | ~ m1_pre_topc(B_77,'#skF_1')
      | v2_struct_0(B_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_8021])).

tff(c_8067,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_8022])).

tff(c_8087,plain,
    ( m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_4'),'#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | r1_tsep_1('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2900,c_8067])).

tff(c_8114,plain,
    ( m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_4'),'#skF_1')
    | r1_tsep_1('#skF_4','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_7784,c_8087])).

tff(c_8115,plain,
    ( m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_4'),'#skF_1')
    | r1_tsep_1('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_8114])).

tff(c_8229,plain,(
    r1_tsep_1('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8115])).

tff(c_8231,plain,(
    ! [A_7] :
      ( ~ m1_pre_topc('#skF_4','#skF_4')
      | ~ m1_pre_topc('#skF_4',A_7)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(resolution,[status(thm)],[c_8229,c_8])).

tff(c_8236,plain,(
    ! [A_7] :
      ( ~ m1_pre_topc('#skF_4',A_7)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7784,c_8231])).

tff(c_8243,plain,(
    ! [A_284] :
      ( ~ m1_pre_topc('#skF_4',A_284)
      | ~ l1_pre_topc(A_284)
      | ~ v2_pre_topc(A_284)
      | v2_struct_0(A_284) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_8236])).

tff(c_8253,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_8243])).

tff(c_8264,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_8253])).

tff(c_8266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_8264])).

tff(c_8268,plain,(
    ~ r1_tsep_1('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_8115])).

tff(c_139,plain,(
    ! [B_82] :
      ( k2_tsep_1('#skF_1',B_82,'#skF_4') = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ m1_pre_topc('#skF_4',B_82)
      | r1_tsep_1(B_82,'#skF_4')
      | ~ m1_pre_topc(B_82,'#skF_1')
      | v2_struct_0(B_82) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_32,c_128])).

tff(c_155,plain,(
    ! [B_82,A_7] :
      ( ~ m1_pre_topc(B_82,A_7)
      | ~ m1_pre_topc('#skF_4',A_7)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7)
      | k2_tsep_1('#skF_1',B_82,'#skF_4') = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ m1_pre_topc('#skF_4',B_82)
      | ~ m1_pre_topc(B_82,'#skF_1')
      | v2_struct_0(B_82) ) ),
    inference(resolution,[status(thm)],[c_139,c_6])).

tff(c_12608,plain,(
    ! [B_344,A_345] :
      ( ~ m1_pre_topc(B_344,A_345)
      | ~ m1_pre_topc('#skF_4',A_345)
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345)
      | k2_tsep_1('#skF_1',B_344,'#skF_4') = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ m1_pre_topc('#skF_4',B_344)
      | ~ m1_pre_topc(B_344,'#skF_1')
      | v2_struct_0(B_344) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_155])).

tff(c_12698,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k2_tsep_1('#skF_1','#skF_1','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3668,c_12608])).

tff(c_12872,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k2_tsep_1('#skF_1','#skF_1','#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3668,c_30,c_44,c_42,c_12698])).

tff(c_12873,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k2_tsep_1('#skF_1','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_12872])).

tff(c_13325,plain,
    ( k2_tsep_1('#skF_1','#skF_1','#skF_4') = k2_tsep_1('#skF_1','#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | r1_tsep_1('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2900,c_12873])).

tff(c_13379,plain,
    ( k2_tsep_1('#skF_1','#skF_1','#skF_4') = k2_tsep_1('#skF_1','#skF_4','#skF_4')
    | r1_tsep_1('#skF_4','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_7784,c_13325])).

tff(c_13380,plain,(
    k2_tsep_1('#skF_1','#skF_1','#skF_4') = k2_tsep_1('#skF_1','#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_8268,c_13379])).

tff(c_13775,plain,(
    ! [B_30,C_38] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_30,C_38),k2_tsep_1('#skF_1','#skF_4','#skF_4'))
      | r1_tsep_1(B_30,C_38)
      | ~ m1_pre_topc(C_38,'#skF_4')
      | ~ m1_pre_topc(B_30,'#skF_1')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(C_38,'#skF_1')
      | v2_struct_0(C_38)
      | ~ m1_pre_topc(B_30,'#skF_1')
      | v2_struct_0(B_30)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13380,c_10])).

tff(c_13830,plain,(
    ! [B_30,C_38] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_30,C_38),k2_tsep_1('#skF_1','#skF_4','#skF_4'))
      | r1_tsep_1(B_30,C_38)
      | ~ m1_pre_topc(C_38,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_38,'#skF_1')
      | v2_struct_0(C_38)
      | ~ m1_pre_topc(B_30,'#skF_1')
      | v2_struct_0(B_30)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3668,c_30,c_13775])).

tff(c_22090,plain,(
    ! [B_430,C_431] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_430,C_431),k2_tsep_1('#skF_1','#skF_4','#skF_4'))
      | r1_tsep_1(B_430,C_431)
      | ~ m1_pre_topc(C_431,'#skF_4')
      | ~ m1_pre_topc(C_431,'#skF_1')
      | v2_struct_0(C_431)
      | ~ m1_pre_topc(B_430,'#skF_1')
      | v2_struct_0(B_430) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_32,c_13830])).

tff(c_3172,plain,(
    ! [B_171] :
      ( g1_pre_topc(u1_struct_0(B_171),u1_pre_topc(B_171)) = k2_tsep_1('#skF_1',B_171,'#skF_4')
      | ~ m1_pre_topc(B_171,'#skF_4')
      | r1_tsep_1(B_171,'#skF_4')
      | ~ m1_pre_topc(B_171,'#skF_1')
      | v2_struct_0(B_171) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_32,c_2899])).

tff(c_3200,plain,(
    ! [B_6,B_171] :
      ( m1_pre_topc(B_6,B_171)
      | ~ m1_pre_topc(B_6,k2_tsep_1('#skF_1',B_171,'#skF_4'))
      | ~ l1_pre_topc(B_171)
      | ~ m1_pre_topc(B_171,'#skF_4')
      | r1_tsep_1(B_171,'#skF_4')
      | ~ m1_pre_topc(B_171,'#skF_1')
      | v2_struct_0(B_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3172,c_4])).

tff(c_22096,plain,(
    ! [B_430,C_431] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_430,C_431),'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | r1_tsep_1('#skF_4','#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | r1_tsep_1(B_430,C_431)
      | ~ m1_pre_topc(C_431,'#skF_4')
      | ~ m1_pre_topc(C_431,'#skF_1')
      | v2_struct_0(C_431)
      | ~ m1_pre_topc(B_430,'#skF_1')
      | v2_struct_0(B_430) ) ),
    inference(resolution,[status(thm)],[c_22090,c_3200])).

tff(c_22196,plain,(
    ! [B_430,C_431] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_430,C_431),'#skF_4')
      | r1_tsep_1('#skF_4','#skF_4')
      | v2_struct_0('#skF_4')
      | r1_tsep_1(B_430,C_431)
      | ~ m1_pre_topc(C_431,'#skF_4')
      | ~ m1_pre_topc(C_431,'#skF_1')
      | v2_struct_0(C_431)
      | ~ m1_pre_topc(B_430,'#skF_1')
      | v2_struct_0(B_430) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_7784,c_72,c_22096])).

tff(c_22731,plain,(
    ! [B_439,C_440] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_439,C_440),'#skF_4')
      | r1_tsep_1(B_439,C_440)
      | ~ m1_pre_topc(C_440,'#skF_4')
      | ~ m1_pre_topc(C_440,'#skF_1')
      | v2_struct_0(C_440)
      | ~ m1_pre_topc(B_439,'#skF_1')
      | v2_struct_0(B_439) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_8268,c_22196])).

tff(c_22,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_22741,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22731,c_22])).

tff(c_22835,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_26,c_22741])).

tff(c_22837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_36,c_24,c_22835])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.80/6.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.80/6.42  
% 14.80/6.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.80/6.42  %$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 14.80/6.42  
% 14.80/6.42  %Foreground sorts:
% 14.80/6.42  
% 14.80/6.42  
% 14.80/6.42  %Background operators:
% 14.80/6.42  
% 14.80/6.42  
% 14.80/6.42  %Foreground operators:
% 14.80/6.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 14.80/6.42  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 14.80/6.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.80/6.42  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 14.80/6.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.80/6.42  tff('#skF_2', type, '#skF_2': $i).
% 14.80/6.42  tff('#skF_3', type, '#skF_3': $i).
% 14.80/6.42  tff('#skF_1', type, '#skF_1': $i).
% 14.80/6.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.80/6.42  tff('#skF_4', type, '#skF_4': $i).
% 14.80/6.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.80/6.42  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 14.80/6.42  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 14.80/6.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 14.80/6.42  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 14.80/6.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.80/6.42  
% 14.99/6.45  tff(f_181, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, D) & m1_pre_topc(C, D)) => (r1_tsep_1(B, C) | m1_pre_topc(k2_tsep_1(A, B, C), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tmap_1)).
% 14.99/6.45  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 14.99/6.45  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 14.99/6.45  tff(f_147, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => ((((m1_pre_topc(B, C) => (k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))) & ((k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => m1_pre_topc(B, C))) & (m1_pre_topc(C, B) => (k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))))) & ((k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => m1_pre_topc(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tsep_1)).
% 14.99/6.45  tff(f_66, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tmap_1)).
% 14.99/6.45  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 14.99/6.45  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(B, D) & m1_pre_topc(C, E)) => (r1_tsep_1(B, C) | m1_pre_topc(k2_tsep_1(A, B, C), k2_tsep_1(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tmap_1)).
% 14.99/6.45  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 14.99/6.45  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 14.99/6.45  tff(c_24, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 14.99/6.45  tff(c_38, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 14.99/6.45  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 14.99/6.45  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 14.99/6.45  tff(c_32, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 14.99/6.45  tff(c_46, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 14.99/6.45  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 14.99/6.45  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 14.99/6.45  tff(c_30, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 14.99/6.45  tff(c_48, plain, (![B_65, A_66]: (l1_pre_topc(B_65) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.99/6.45  tff(c_60, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_48])).
% 14.99/6.45  tff(c_72, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_60])).
% 14.99/6.45  tff(c_12, plain, (![A_45]: (m1_pre_topc(A_45, A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.99/6.45  tff(c_2848, plain, (![A_160, B_161, C_162]: (k2_tsep_1(A_160, B_161, C_162)=g1_pre_topc(u1_struct_0(B_161), u1_pre_topc(B_161)) | ~m1_pre_topc(B_161, C_162) | r1_tsep_1(B_161, C_162) | ~m1_pre_topc(C_162, A_160) | v2_struct_0(C_162) | ~m1_pre_topc(B_161, A_160) | v2_struct_0(B_161) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_147])).
% 14.99/6.45  tff(c_2866, plain, (![B_161]: (g1_pre_topc(u1_struct_0(B_161), u1_pre_topc(B_161))=k2_tsep_1('#skF_1', B_161, '#skF_4') | ~m1_pre_topc(B_161, '#skF_4') | r1_tsep_1(B_161, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_161, '#skF_1') | v2_struct_0(B_161) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_2848])).
% 14.99/6.45  tff(c_2899, plain, (![B_161]: (g1_pre_topc(u1_struct_0(B_161), u1_pre_topc(B_161))=k2_tsep_1('#skF_1', B_161, '#skF_4') | ~m1_pre_topc(B_161, '#skF_4') | r1_tsep_1(B_161, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_161, '#skF_1') | v2_struct_0(B_161) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_2866])).
% 14.99/6.45  tff(c_2900, plain, (![B_161]: (g1_pre_topc(u1_struct_0(B_161), u1_pre_topc(B_161))=k2_tsep_1('#skF_1', B_161, '#skF_4') | ~m1_pre_topc(B_161, '#skF_4') | r1_tsep_1(B_161, '#skF_4') | ~m1_pre_topc(B_161, '#skF_1') | v2_struct_0(B_161))), inference(negUnitSimplification, [status(thm)], [c_46, c_32, c_2899])).
% 14.99/6.45  tff(c_101, plain, (![A_76, B_77, C_78]: (k2_tsep_1(A_76, B_77, C_78)=g1_pre_topc(u1_struct_0(C_78), u1_pre_topc(C_78)) | ~m1_pre_topc(C_78, B_77) | r1_tsep_1(B_77, C_78) | ~m1_pre_topc(C_78, A_76) | v2_struct_0(C_78) | ~m1_pre_topc(B_77, A_76) | v2_struct_0(B_77) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_147])).
% 14.99/6.45  tff(c_111, plain, (![B_77]: (k2_tsep_1('#skF_1', B_77, '#skF_4')=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~m1_pre_topc('#skF_4', B_77) | r1_tsep_1(B_77, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_101])).
% 14.99/6.45  tff(c_128, plain, (![B_77]: (k2_tsep_1('#skF_1', B_77, '#skF_4')=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~m1_pre_topc('#skF_4', B_77) | r1_tsep_1(B_77, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_111])).
% 14.99/6.45  tff(c_129, plain, (![B_77]: (k2_tsep_1('#skF_1', B_77, '#skF_4')=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~m1_pre_topc('#skF_4', B_77) | r1_tsep_1(B_77, '#skF_4') | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77))), inference(negUnitSimplification, [status(thm)], [c_46, c_32, c_128])).
% 14.99/6.45  tff(c_115, plain, (![B_77]: (k2_tsep_1('#skF_1', B_77, '#skF_3')=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc('#skF_3', B_77) | r1_tsep_1(B_77, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_101])).
% 14.99/6.45  tff(c_136, plain, (![B_77]: (k2_tsep_1('#skF_1', B_77, '#skF_3')=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc('#skF_3', B_77) | r1_tsep_1(B_77, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_115])).
% 14.99/6.45  tff(c_173, plain, (![B_83]: (k2_tsep_1('#skF_1', B_83, '#skF_3')=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc('#skF_3', B_83) | r1_tsep_1(B_83, '#skF_3') | ~m1_pre_topc(B_83, '#skF_1') | v2_struct_0(B_83))), inference(negUnitSimplification, [status(thm)], [c_46, c_36, c_136])).
% 14.99/6.45  tff(c_6, plain, (![C_13, B_11, A_7]: (~r1_tsep_1(C_13, B_11) | ~m1_pre_topc(B_11, C_13) | ~m1_pre_topc(C_13, A_7) | v2_struct_0(C_13) | ~m1_pre_topc(B_11, A_7) | v2_struct_0(B_11) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.99/6.45  tff(c_189, plain, (![B_83, A_7]: (~m1_pre_topc(B_83, A_7) | ~m1_pre_topc('#skF_3', A_7) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7) | k2_tsep_1('#skF_1', B_83, '#skF_3')=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc('#skF_3', B_83) | ~m1_pre_topc(B_83, '#skF_1') | v2_struct_0(B_83))), inference(resolution, [status(thm)], [c_173, c_6])).
% 14.99/6.45  tff(c_361, plain, (![B_97, A_98]: (~m1_pre_topc(B_97, A_98) | ~m1_pre_topc('#skF_3', A_98) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98) | k2_tsep_1('#skF_1', B_97, '#skF_3')=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc('#skF_3', B_97) | ~m1_pre_topc(B_97, '#skF_1') | v2_struct_0(B_97))), inference(negUnitSimplification, [status(thm)], [c_36, c_189])).
% 14.99/6.45  tff(c_377, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k2_tsep_1('#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_361])).
% 14.99/6.45  tff(c_406, plain, (v2_struct_0('#skF_1') | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k2_tsep_1('#skF_1', '#skF_4', '#skF_3') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_44, c_42, c_34, c_377])).
% 14.99/6.45  tff(c_407, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k2_tsep_1('#skF_1', '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_32, c_46, c_406])).
% 14.99/6.45  tff(c_395, plain, (![A_45]: (~v2_pre_topc(A_45) | k2_tsep_1('#skF_1', A_45, '#skF_3')=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc('#skF_3', A_45) | ~m1_pre_topc(A_45, '#skF_1') | v2_struct_0(A_45) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_12, c_361])).
% 14.99/6.45  tff(c_3633, plain, (![A_180]: (~v2_pre_topc(A_180) | k2_tsep_1('#skF_1', A_180, '#skF_3')=k2_tsep_1('#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', A_180) | ~m1_pre_topc(A_180, '#skF_1') | v2_struct_0(A_180) | ~l1_pre_topc(A_180))), inference(demodulation, [status(thm), theory('equality')], [c_407, c_395])).
% 14.99/6.45  tff(c_3642, plain, (~v2_pre_topc('#skF_1') | k2_tsep_1('#skF_1', '#skF_1', '#skF_3')=k2_tsep_1('#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_3633])).
% 14.99/6.45  tff(c_3657, plain, (k2_tsep_1('#skF_1', '#skF_1', '#skF_3')=k2_tsep_1('#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_3642])).
% 14.99/6.45  tff(c_3658, plain, (k2_tsep_1('#skF_1', '#skF_1', '#skF_3')=k2_tsep_1('#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_46, c_3657])).
% 14.99/6.45  tff(c_3659, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_3658])).
% 14.99/6.45  tff(c_3662, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_3659])).
% 14.99/6.45  tff(c_3666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_3662])).
% 14.99/6.45  tff(c_3668, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_3658])).
% 14.99/6.45  tff(c_20, plain, (![A_46, B_50, C_52]: (k2_tsep_1(A_46, B_50, C_52)=g1_pre_topc(u1_struct_0(B_50), u1_pre_topc(B_50)) | ~m1_pre_topc(B_50, C_52) | r1_tsep_1(B_50, C_52) | ~m1_pre_topc(C_52, A_46) | v2_struct_0(C_52) | ~m1_pre_topc(B_50, A_46) | v2_struct_0(B_50) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_147])).
% 14.99/6.45  tff(c_3670, plain, (![B_50]: (g1_pre_topc(u1_struct_0(B_50), u1_pre_topc(B_50))=k2_tsep_1('#skF_1', B_50, '#skF_1') | r1_tsep_1(B_50, '#skF_1') | ~m1_pre_topc(B_50, '#skF_1') | v2_struct_0(B_50) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_3668, c_20])).
% 14.99/6.45  tff(c_3678, plain, (![B_50]: (g1_pre_topc(u1_struct_0(B_50), u1_pre_topc(B_50))=k2_tsep_1('#skF_1', B_50, '#skF_1') | r1_tsep_1(B_50, '#skF_1') | ~m1_pre_topc(B_50, '#skF_1') | v2_struct_0(B_50) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3670])).
% 14.99/6.45  tff(c_3679, plain, (![B_50]: (g1_pre_topc(u1_struct_0(B_50), u1_pre_topc(B_50))=k2_tsep_1('#skF_1', B_50, '#skF_1') | r1_tsep_1(B_50, '#skF_1') | ~m1_pre_topc(B_50, '#skF_1') | v2_struct_0(B_50))), inference(negUnitSimplification, [status(thm)], [c_46, c_3678])).
% 14.99/6.45  tff(c_117, plain, (![A_45, B_77]: (k2_tsep_1(A_45, B_77, A_45)=g1_pre_topc(u1_struct_0(A_45), u1_pre_topc(A_45)) | ~m1_pre_topc(A_45, B_77) | r1_tsep_1(B_77, A_45) | ~m1_pre_topc(B_77, A_45) | v2_struct_0(B_77) | ~v2_pre_topc(A_45) | v2_struct_0(A_45) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_12, c_101])).
% 14.99/6.45  tff(c_16, plain, (![A_46, B_50, C_52]: (k2_tsep_1(A_46, B_50, C_52)=g1_pre_topc(u1_struct_0(C_52), u1_pre_topc(C_52)) | ~m1_pre_topc(C_52, B_50) | r1_tsep_1(B_50, C_52) | ~m1_pre_topc(C_52, A_46) | v2_struct_0(C_52) | ~m1_pre_topc(B_50, A_46) | v2_struct_0(B_50) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_147])).
% 14.99/6.45  tff(c_3672, plain, (![B_50]: (k2_tsep_1('#skF_1', B_50, '#skF_1')=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~m1_pre_topc('#skF_1', B_50) | r1_tsep_1(B_50, '#skF_1') | ~m1_pre_topc(B_50, '#skF_1') | v2_struct_0(B_50) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_3668, c_16])).
% 14.99/6.45  tff(c_3682, plain, (![B_50]: (k2_tsep_1('#skF_1', B_50, '#skF_1')=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~m1_pre_topc('#skF_1', B_50) | r1_tsep_1(B_50, '#skF_1') | ~m1_pre_topc(B_50, '#skF_1') | v2_struct_0(B_50) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3672])).
% 14.99/6.45  tff(c_3973, plain, (![B_190]: (k2_tsep_1('#skF_1', B_190, '#skF_1')=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~m1_pre_topc('#skF_1', B_190) | r1_tsep_1(B_190, '#skF_1') | ~m1_pre_topc(B_190, '#skF_1') | v2_struct_0(B_190))), inference(negUnitSimplification, [status(thm)], [c_46, c_3682])).
% 14.99/6.45  tff(c_4, plain, (![B_6, A_4]: (m1_pre_topc(B_6, A_4) | ~m1_pre_topc(B_6, g1_pre_topc(u1_struct_0(A_4), u1_pre_topc(A_4))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.99/6.45  tff(c_4019, plain, (![B_6, B_190]: (m1_pre_topc(B_6, '#skF_1') | ~m1_pre_topc(B_6, k2_tsep_1('#skF_1', B_190, '#skF_1')) | ~l1_pre_topc('#skF_1') | ~m1_pre_topc('#skF_1', B_190) | r1_tsep_1(B_190, '#skF_1') | ~m1_pre_topc(B_190, '#skF_1') | v2_struct_0(B_190))), inference(superposition, [status(thm), theory('equality')], [c_3973, c_4])).
% 14.99/6.45  tff(c_4115, plain, (![B_191, B_192]: (m1_pre_topc(B_191, '#skF_1') | ~m1_pre_topc(B_191, k2_tsep_1('#skF_1', B_192, '#skF_1')) | ~m1_pre_topc('#skF_1', B_192) | r1_tsep_1(B_192, '#skF_1') | ~m1_pre_topc(B_192, '#skF_1') | v2_struct_0(B_192))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4019])).
% 14.99/6.45  tff(c_4125, plain, (![B_191, B_77]: (m1_pre_topc(B_191, '#skF_1') | ~m1_pre_topc(B_191, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc('#skF_1', B_77) | r1_tsep_1(B_77, '#skF_1') | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77) | ~m1_pre_topc('#skF_1', B_77) | r1_tsep_1(B_77, '#skF_1') | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77) | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_4115])).
% 14.99/6.45  tff(c_4144, plain, (![B_191, B_77]: (m1_pre_topc(B_191, '#skF_1') | ~m1_pre_topc(B_191, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc('#skF_1', B_77) | r1_tsep_1(B_77, '#skF_1') | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_4125])).
% 14.99/6.45  tff(c_4145, plain, (![B_191, B_77]: (m1_pre_topc(B_191, '#skF_1') | ~m1_pre_topc(B_191, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc('#skF_1', B_77) | r1_tsep_1(B_77, '#skF_1') | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77))), inference(negUnitSimplification, [status(thm)], [c_46, c_4144])).
% 14.99/6.45  tff(c_4313, plain, (![B_202]: (~m1_pre_topc('#skF_1', B_202) | r1_tsep_1(B_202, '#skF_1') | ~m1_pre_topc(B_202, '#skF_1') | v2_struct_0(B_202))), inference(splitLeft, [status(thm)], [c_4145])).
% 14.99/6.45  tff(c_8, plain, (![B_11, C_13, A_7]: (~r1_tsep_1(B_11, C_13) | ~m1_pre_topc(B_11, C_13) | ~m1_pre_topc(C_13, A_7) | v2_struct_0(C_13) | ~m1_pre_topc(B_11, A_7) | v2_struct_0(B_11) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.99/6.45  tff(c_4318, plain, (![A_7, B_202]: (~m1_pre_topc('#skF_1', A_7) | v2_struct_0('#skF_1') | ~m1_pre_topc(B_202, A_7) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7) | ~m1_pre_topc('#skF_1', B_202) | ~m1_pre_topc(B_202, '#skF_1') | v2_struct_0(B_202))), inference(resolution, [status(thm)], [c_4313, c_8])).
% 14.99/6.45  tff(c_4569, plain, (![A_209, B_210]: (~m1_pre_topc('#skF_1', A_209) | ~m1_pre_topc(B_210, A_209) | ~l1_pre_topc(A_209) | ~v2_pre_topc(A_209) | v2_struct_0(A_209) | ~m1_pre_topc('#skF_1', B_210) | ~m1_pre_topc(B_210, '#skF_1') | v2_struct_0(B_210))), inference(negUnitSimplification, [status(thm)], [c_46, c_4318])).
% 14.99/6.45  tff(c_4571, plain, (![B_210]: (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_1', B_210) | ~m1_pre_topc(B_210, '#skF_1') | v2_struct_0(B_210))), inference(resolution, [status(thm)], [c_3668, c_4569])).
% 14.99/6.45  tff(c_4577, plain, (![B_210]: (v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_1', B_210) | ~m1_pre_topc(B_210, '#skF_1') | v2_struct_0(B_210))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_4571])).
% 14.99/6.45  tff(c_4583, plain, (![B_211]: (~m1_pre_topc('#skF_1', B_211) | ~m1_pre_topc(B_211, '#skF_1') | v2_struct_0(B_211))), inference(negUnitSimplification, [status(thm)], [c_46, c_4577])).
% 14.99/6.45  tff(c_4585, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3668, c_4583])).
% 14.99/6.45  tff(c_4591, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3668, c_4585])).
% 14.99/6.45  tff(c_4593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_4591])).
% 14.99/6.45  tff(c_4595, plain, (![B_212]: (m1_pre_topc(B_212, '#skF_1') | ~m1_pre_topc(B_212, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitRight, [status(thm)], [c_4145])).
% 14.99/6.45  tff(c_4599, plain, (![B_212]: (m1_pre_topc(B_212, '#skF_1') | ~m1_pre_topc(B_212, k2_tsep_1('#skF_1', '#skF_1', '#skF_1')) | r1_tsep_1('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3679, c_4595])).
% 14.99/6.45  tff(c_4624, plain, (![B_212]: (m1_pre_topc(B_212, '#skF_1') | ~m1_pre_topc(B_212, k2_tsep_1('#skF_1', '#skF_1', '#skF_1')) | r1_tsep_1('#skF_1', '#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3668, c_4599])).
% 14.99/6.45  tff(c_4625, plain, (![B_212]: (m1_pre_topc(B_212, '#skF_1') | ~m1_pre_topc(B_212, k2_tsep_1('#skF_1', '#skF_1', '#skF_1')) | r1_tsep_1('#skF_1', '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_46, c_4624])).
% 14.99/6.45  tff(c_4641, plain, (r1_tsep_1('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_4625])).
% 14.99/6.45  tff(c_4643, plain, (![A_7]: (~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_1', A_7) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(resolution, [status(thm)], [c_4641, c_8])).
% 14.99/6.45  tff(c_4648, plain, (![A_7]: (~m1_pre_topc('#skF_1', A_7) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_3668, c_4643])).
% 14.99/6.45  tff(c_4654, plain, (![A_213]: (~m1_pre_topc('#skF_1', A_213) | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213) | v2_struct_0(A_213))), inference(negUnitSimplification, [status(thm)], [c_46, c_4648])).
% 14.99/6.45  tff(c_4657, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3668, c_4654])).
% 14.99/6.45  tff(c_4664, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_4657])).
% 14.99/6.45  tff(c_4666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_4664])).
% 14.99/6.45  tff(c_4668, plain, (~r1_tsep_1('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_4625])).
% 14.99/6.45  tff(c_4672, plain, (![B_214]: (m1_pre_topc(B_214, '#skF_1') | ~m1_pre_topc(B_214, k2_tsep_1('#skF_1', '#skF_1', '#skF_1')))), inference(splitRight, [status(thm)], [c_4625])).
% 14.99/6.45  tff(c_4690, plain, (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_1', '#skF_1'), '#skF_1') | ~l1_pre_topc(k2_tsep_1('#skF_1', '#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_12, c_4672])).
% 14.99/6.45  tff(c_4691, plain, (~l1_pre_topc(k2_tsep_1('#skF_1', '#skF_1', '#skF_1'))), inference(splitLeft, [status(thm)], [c_4690])).
% 14.99/6.45  tff(c_10, plain, (![E_44, D_42, C_38, A_14, B_30]: (m1_pre_topc(k2_tsep_1(A_14, B_30, C_38), k2_tsep_1(A_14, D_42, E_44)) | r1_tsep_1(B_30, C_38) | ~m1_pre_topc(C_38, E_44) | ~m1_pre_topc(B_30, D_42) | ~m1_pre_topc(E_44, A_14) | v2_struct_0(E_44) | ~m1_pre_topc(D_42, A_14) | v2_struct_0(D_42) | ~m1_pre_topc(C_38, A_14) | v2_struct_0(C_38) | ~m1_pre_topc(B_30, A_14) | v2_struct_0(B_30) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_105])).
% 14.99/6.45  tff(c_4676, plain, (![B_30, C_38]: (m1_pre_topc(k2_tsep_1('#skF_1', B_30, C_38), '#skF_1') | r1_tsep_1(B_30, C_38) | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc(C_38, '#skF_1') | v2_struct_0(C_38) | ~m1_pre_topc(B_30, '#skF_1') | v2_struct_0(B_30) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_4672])).
% 14.99/6.45  tff(c_4687, plain, (![B_30, C_38]: (m1_pre_topc(k2_tsep_1('#skF_1', B_30, C_38), '#skF_1') | r1_tsep_1(B_30, C_38) | ~m1_pre_topc(C_38, '#skF_1') | v2_struct_0(C_38) | ~m1_pre_topc(B_30, '#skF_1') | v2_struct_0(B_30) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3668, c_4676])).
% 14.99/6.45  tff(c_5419, plain, (![B_229, C_230]: (m1_pre_topc(k2_tsep_1('#skF_1', B_229, C_230), '#skF_1') | r1_tsep_1(B_229, C_230) | ~m1_pre_topc(C_230, '#skF_1') | v2_struct_0(C_230) | ~m1_pre_topc(B_229, '#skF_1') | v2_struct_0(B_229))), inference(negUnitSimplification, [status(thm)], [c_46, c_4687])).
% 14.99/6.45  tff(c_2, plain, (![B_3, A_1]: (l1_pre_topc(B_3) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.99/6.45  tff(c_5426, plain, (![B_229, C_230]: (l1_pre_topc(k2_tsep_1('#skF_1', B_229, C_230)) | ~l1_pre_topc('#skF_1') | r1_tsep_1(B_229, C_230) | ~m1_pre_topc(C_230, '#skF_1') | v2_struct_0(C_230) | ~m1_pre_topc(B_229, '#skF_1') | v2_struct_0(B_229))), inference(resolution, [status(thm)], [c_5419, c_2])).
% 14.99/6.45  tff(c_5517, plain, (![B_231, C_232]: (l1_pre_topc(k2_tsep_1('#skF_1', B_231, C_232)) | r1_tsep_1(B_231, C_232) | ~m1_pre_topc(C_232, '#skF_1') | v2_struct_0(C_232) | ~m1_pre_topc(B_231, '#skF_1') | v2_struct_0(B_231))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5426])).
% 14.99/6.45  tff(c_2888, plain, (![A_45, B_161]: (k2_tsep_1(A_45, B_161, A_45)=g1_pre_topc(u1_struct_0(B_161), u1_pre_topc(B_161)) | r1_tsep_1(B_161, A_45) | ~m1_pre_topc(B_161, A_45) | v2_struct_0(B_161) | ~v2_pre_topc(A_45) | v2_struct_0(A_45) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_12, c_2848])).
% 14.99/6.45  tff(c_4640, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_1') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_4595])).
% 14.99/6.45  tff(c_4949, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_4640])).
% 14.99/6.45  tff(c_4959, plain, (![A_45]: (~l1_pre_topc(k2_tsep_1(A_45, '#skF_1', A_45)) | r1_tsep_1('#skF_1', A_45) | ~m1_pre_topc('#skF_1', A_45) | v2_struct_0('#skF_1') | ~v2_pre_topc(A_45) | v2_struct_0(A_45) | ~l1_pre_topc(A_45))), inference(superposition, [status(thm), theory('equality')], [c_2888, c_4949])).
% 14.99/6.45  tff(c_4975, plain, (![A_45]: (~l1_pre_topc(k2_tsep_1(A_45, '#skF_1', A_45)) | r1_tsep_1('#skF_1', A_45) | ~m1_pre_topc('#skF_1', A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45) | ~l1_pre_topc(A_45))), inference(negUnitSimplification, [status(thm)], [c_46, c_4959])).
% 14.99/6.45  tff(c_5521, plain, (~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | r1_tsep_1('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_5517, c_4975])).
% 14.99/6.45  tff(c_5563, plain, (r1_tsep_1('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3668, c_42, c_44, c_5521])).
% 14.99/6.45  tff(c_5565, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_4668, c_5563])).
% 14.99/6.45  tff(c_5567, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_4640])).
% 14.99/6.45  tff(c_5949, plain, (l1_pre_topc(k2_tsep_1('#skF_1', '#skF_1', '#skF_1')) | r1_tsep_1('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3679, c_5567])).
% 14.99/6.45  tff(c_5966, plain, (l1_pre_topc(k2_tsep_1('#skF_1', '#skF_1', '#skF_1')) | r1_tsep_1('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3668, c_5949])).
% 14.99/6.45  tff(c_5968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_4668, c_4691, c_5966])).
% 14.99/6.45  tff(c_5970, plain, (l1_pre_topc(k2_tsep_1('#skF_1', '#skF_1', '#skF_1'))), inference(splitRight, [status(thm)], [c_4690])).
% 14.99/6.45  tff(c_2977, plain, (![D_166, E_164, C_167, B_165, A_168]: (m1_pre_topc(k2_tsep_1(A_168, B_165, C_167), k2_tsep_1(A_168, D_166, E_164)) | r1_tsep_1(B_165, C_167) | ~m1_pre_topc(C_167, E_164) | ~m1_pre_topc(B_165, D_166) | ~m1_pre_topc(E_164, A_168) | v2_struct_0(E_164) | ~m1_pre_topc(D_166, A_168) | v2_struct_0(D_166) | ~m1_pre_topc(C_167, A_168) | v2_struct_0(C_167) | ~m1_pre_topc(B_165, A_168) | v2_struct_0(B_165) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_105])).
% 14.99/6.45  tff(c_3037, plain, (![D_166, E_164, C_167, B_165, A_168]: (l1_pre_topc(k2_tsep_1(A_168, B_165, C_167)) | ~l1_pre_topc(k2_tsep_1(A_168, D_166, E_164)) | r1_tsep_1(B_165, C_167) | ~m1_pre_topc(C_167, E_164) | ~m1_pre_topc(B_165, D_166) | ~m1_pre_topc(E_164, A_168) | v2_struct_0(E_164) | ~m1_pre_topc(D_166, A_168) | v2_struct_0(D_166) | ~m1_pre_topc(C_167, A_168) | v2_struct_0(C_167) | ~m1_pre_topc(B_165, A_168) | v2_struct_0(B_165) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(resolution, [status(thm)], [c_2977, c_2])).
% 14.99/6.45  tff(c_5972, plain, (![B_165, C_167]: (l1_pre_topc(k2_tsep_1('#skF_1', B_165, C_167)) | r1_tsep_1(B_165, C_167) | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc(C_167, '#skF_1') | v2_struct_0(C_167) | ~m1_pre_topc(B_165, '#skF_1') | v2_struct_0(B_165) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_5970, c_3037])).
% 14.99/6.45  tff(c_5975, plain, (![B_165, C_167]: (l1_pre_topc(k2_tsep_1('#skF_1', B_165, C_167)) | r1_tsep_1(B_165, C_167) | ~m1_pre_topc(C_167, '#skF_1') | v2_struct_0(C_167) | ~m1_pre_topc(B_165, '#skF_1') | v2_struct_0(B_165) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3668, c_5972])).
% 14.99/6.45  tff(c_6852, plain, (![B_255, C_256]: (l1_pre_topc(k2_tsep_1('#skF_1', B_255, C_256)) | r1_tsep_1(B_255, C_256) | ~m1_pre_topc(C_256, '#skF_1') | v2_struct_0(C_256) | ~m1_pre_topc(B_255, '#skF_1') | v2_struct_0(B_255))), inference(negUnitSimplification, [status(thm)], [c_46, c_5975])).
% 14.99/6.45  tff(c_6884, plain, (![B_77]: (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | r1_tsep_1(B_77, '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77) | ~m1_pre_topc('#skF_4', B_77) | r1_tsep_1(B_77, '#skF_4') | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77))), inference(superposition, [status(thm), theory('equality')], [c_129, c_6852])).
% 14.99/6.45  tff(c_6914, plain, (![B_77]: (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', B_77) | r1_tsep_1(B_77, '#skF_4') | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_6884])).
% 14.99/6.45  tff(c_6915, plain, (![B_77]: (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc('#skF_4', B_77) | r1_tsep_1(B_77, '#skF_4') | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77))), inference(negUnitSimplification, [status(thm)], [c_32, c_6914])).
% 14.99/6.45  tff(c_6917, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_6915])).
% 14.99/6.45  tff(c_6964, plain, (l1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_4') | r1_tsep_1('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2900, c_6917])).
% 14.99/6.45  tff(c_6980, plain, (l1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_4') | r1_tsep_1('#skF_4', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_6964])).
% 14.99/6.45  tff(c_6981, plain, (l1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_4') | r1_tsep_1('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_6980])).
% 14.99/6.45  tff(c_7775, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_6981])).
% 14.99/6.45  tff(c_7778, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_7775])).
% 14.99/6.45  tff(c_7782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_7778])).
% 14.99/6.45  tff(c_7784, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_6981])).
% 14.99/6.45  tff(c_7947, plain, (![B_280, C_281]: (m1_pre_topc(k2_tsep_1('#skF_1', B_280, C_281), '#skF_1') | r1_tsep_1(B_280, C_281) | ~m1_pre_topc(C_281, '#skF_1') | v2_struct_0(C_281) | ~m1_pre_topc(B_280, '#skF_1') | v2_struct_0(B_280))), inference(negUnitSimplification, [status(thm)], [c_46, c_4687])).
% 14.99/6.45  tff(c_7984, plain, (![B_77]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_1') | r1_tsep_1(B_77, '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77) | ~m1_pre_topc('#skF_4', B_77) | r1_tsep_1(B_77, '#skF_4') | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77))), inference(superposition, [status(thm), theory('equality')], [c_129, c_7947])).
% 14.99/6.45  tff(c_8021, plain, (![B_77]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', B_77) | r1_tsep_1(B_77, '#skF_4') | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_7984])).
% 14.99/6.45  tff(c_8022, plain, (![B_77]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_1') | ~m1_pre_topc('#skF_4', B_77) | r1_tsep_1(B_77, '#skF_4') | ~m1_pre_topc(B_77, '#skF_1') | v2_struct_0(B_77))), inference(negUnitSimplification, [status(thm)], [c_32, c_8021])).
% 14.99/6.45  tff(c_8067, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_1')), inference(splitLeft, [status(thm)], [c_8022])).
% 14.99/6.45  tff(c_8087, plain, (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_4'), '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_4') | r1_tsep_1('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2900, c_8067])).
% 14.99/6.45  tff(c_8114, plain, (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_4'), '#skF_1') | r1_tsep_1('#skF_4', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_7784, c_8087])).
% 14.99/6.45  tff(c_8115, plain, (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_4'), '#skF_1') | r1_tsep_1('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_8114])).
% 14.99/6.45  tff(c_8229, plain, (r1_tsep_1('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_8115])).
% 14.99/6.45  tff(c_8231, plain, (![A_7]: (~m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', A_7) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(resolution, [status(thm)], [c_8229, c_8])).
% 14.99/6.45  tff(c_8236, plain, (![A_7]: (~m1_pre_topc('#skF_4', A_7) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_7784, c_8231])).
% 14.99/6.45  tff(c_8243, plain, (![A_284]: (~m1_pre_topc('#skF_4', A_284) | ~l1_pre_topc(A_284) | ~v2_pre_topc(A_284) | v2_struct_0(A_284))), inference(negUnitSimplification, [status(thm)], [c_32, c_8236])).
% 14.99/6.45  tff(c_8253, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_8243])).
% 14.99/6.45  tff(c_8264, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_8253])).
% 14.99/6.45  tff(c_8266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_8264])).
% 14.99/6.45  tff(c_8268, plain, (~r1_tsep_1('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_8115])).
% 14.99/6.45  tff(c_139, plain, (![B_82]: (k2_tsep_1('#skF_1', B_82, '#skF_4')=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~m1_pre_topc('#skF_4', B_82) | r1_tsep_1(B_82, '#skF_4') | ~m1_pre_topc(B_82, '#skF_1') | v2_struct_0(B_82))), inference(negUnitSimplification, [status(thm)], [c_46, c_32, c_128])).
% 14.99/6.45  tff(c_155, plain, (![B_82, A_7]: (~m1_pre_topc(B_82, A_7) | ~m1_pre_topc('#skF_4', A_7) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7) | k2_tsep_1('#skF_1', B_82, '#skF_4')=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~m1_pre_topc('#skF_4', B_82) | ~m1_pre_topc(B_82, '#skF_1') | v2_struct_0(B_82))), inference(resolution, [status(thm)], [c_139, c_6])).
% 14.99/6.45  tff(c_12608, plain, (![B_344, A_345]: (~m1_pre_topc(B_344, A_345) | ~m1_pre_topc('#skF_4', A_345) | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345) | v2_struct_0(A_345) | k2_tsep_1('#skF_1', B_344, '#skF_4')=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~m1_pre_topc('#skF_4', B_344) | ~m1_pre_topc(B_344, '#skF_1') | v2_struct_0(B_344))), inference(negUnitSimplification, [status(thm)], [c_32, c_155])).
% 14.99/6.45  tff(c_12698, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k2_tsep_1('#skF_1', '#skF_1', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3668, c_12608])).
% 14.99/6.45  tff(c_12872, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k2_tsep_1('#skF_1', '#skF_1', '#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3668, c_30, c_44, c_42, c_12698])).
% 14.99/6.45  tff(c_12873, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k2_tsep_1('#skF_1', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_12872])).
% 14.99/6.45  tff(c_13325, plain, (k2_tsep_1('#skF_1', '#skF_1', '#skF_4')=k2_tsep_1('#skF_1', '#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | r1_tsep_1('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2900, c_12873])).
% 14.99/6.45  tff(c_13379, plain, (k2_tsep_1('#skF_1', '#skF_1', '#skF_4')=k2_tsep_1('#skF_1', '#skF_4', '#skF_4') | r1_tsep_1('#skF_4', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_7784, c_13325])).
% 14.99/6.45  tff(c_13380, plain, (k2_tsep_1('#skF_1', '#skF_1', '#skF_4')=k2_tsep_1('#skF_1', '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_8268, c_13379])).
% 14.99/6.45  tff(c_13775, plain, (![B_30, C_38]: (m1_pre_topc(k2_tsep_1('#skF_1', B_30, C_38), k2_tsep_1('#skF_1', '#skF_4', '#skF_4')) | r1_tsep_1(B_30, C_38) | ~m1_pre_topc(C_38, '#skF_4') | ~m1_pre_topc(B_30, '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc(C_38, '#skF_1') | v2_struct_0(C_38) | ~m1_pre_topc(B_30, '#skF_1') | v2_struct_0(B_30) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_13380, c_10])).
% 14.99/6.45  tff(c_13830, plain, (![B_30, C_38]: (m1_pre_topc(k2_tsep_1('#skF_1', B_30, C_38), k2_tsep_1('#skF_1', '#skF_4', '#skF_4')) | r1_tsep_1(B_30, C_38) | ~m1_pre_topc(C_38, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(C_38, '#skF_1') | v2_struct_0(C_38) | ~m1_pre_topc(B_30, '#skF_1') | v2_struct_0(B_30) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3668, c_30, c_13775])).
% 14.99/6.45  tff(c_22090, plain, (![B_430, C_431]: (m1_pre_topc(k2_tsep_1('#skF_1', B_430, C_431), k2_tsep_1('#skF_1', '#skF_4', '#skF_4')) | r1_tsep_1(B_430, C_431) | ~m1_pre_topc(C_431, '#skF_4') | ~m1_pre_topc(C_431, '#skF_1') | v2_struct_0(C_431) | ~m1_pre_topc(B_430, '#skF_1') | v2_struct_0(B_430))), inference(negUnitSimplification, [status(thm)], [c_46, c_32, c_13830])).
% 14.99/6.45  tff(c_3172, plain, (![B_171]: (g1_pre_topc(u1_struct_0(B_171), u1_pre_topc(B_171))=k2_tsep_1('#skF_1', B_171, '#skF_4') | ~m1_pre_topc(B_171, '#skF_4') | r1_tsep_1(B_171, '#skF_4') | ~m1_pre_topc(B_171, '#skF_1') | v2_struct_0(B_171))), inference(negUnitSimplification, [status(thm)], [c_46, c_32, c_2899])).
% 14.99/6.45  tff(c_3200, plain, (![B_6, B_171]: (m1_pre_topc(B_6, B_171) | ~m1_pre_topc(B_6, k2_tsep_1('#skF_1', B_171, '#skF_4')) | ~l1_pre_topc(B_171) | ~m1_pre_topc(B_171, '#skF_4') | r1_tsep_1(B_171, '#skF_4') | ~m1_pre_topc(B_171, '#skF_1') | v2_struct_0(B_171))), inference(superposition, [status(thm), theory('equality')], [c_3172, c_4])).
% 14.99/6.45  tff(c_22096, plain, (![B_430, C_431]: (m1_pre_topc(k2_tsep_1('#skF_1', B_430, C_431), '#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | r1_tsep_1('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | r1_tsep_1(B_430, C_431) | ~m1_pre_topc(C_431, '#skF_4') | ~m1_pre_topc(C_431, '#skF_1') | v2_struct_0(C_431) | ~m1_pre_topc(B_430, '#skF_1') | v2_struct_0(B_430))), inference(resolution, [status(thm)], [c_22090, c_3200])).
% 14.99/6.45  tff(c_22196, plain, (![B_430, C_431]: (m1_pre_topc(k2_tsep_1('#skF_1', B_430, C_431), '#skF_4') | r1_tsep_1('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | r1_tsep_1(B_430, C_431) | ~m1_pre_topc(C_431, '#skF_4') | ~m1_pre_topc(C_431, '#skF_1') | v2_struct_0(C_431) | ~m1_pre_topc(B_430, '#skF_1') | v2_struct_0(B_430))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_7784, c_72, c_22096])).
% 14.99/6.45  tff(c_22731, plain, (![B_439, C_440]: (m1_pre_topc(k2_tsep_1('#skF_1', B_439, C_440), '#skF_4') | r1_tsep_1(B_439, C_440) | ~m1_pre_topc(C_440, '#skF_4') | ~m1_pre_topc(C_440, '#skF_1') | v2_struct_0(C_440) | ~m1_pre_topc(B_439, '#skF_1') | v2_struct_0(B_439))), inference(negUnitSimplification, [status(thm)], [c_32, c_8268, c_22196])).
% 14.99/6.45  tff(c_22, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 14.99/6.45  tff(c_22741, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_22731, c_22])).
% 14.99/6.45  tff(c_22835, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_26, c_22741])).
% 14.99/6.45  tff(c_22837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_36, c_24, c_22835])).
% 14.99/6.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.99/6.45  
% 14.99/6.45  Inference rules
% 14.99/6.45  ----------------------
% 14.99/6.45  #Ref     : 0
% 14.99/6.45  #Sup     : 4279
% 14.99/6.45  #Fact    : 10
% 14.99/6.45  #Define  : 0
% 14.99/6.45  #Split   : 99
% 14.99/6.46  #Chain   : 0
% 14.99/6.46  #Close   : 0
% 14.99/6.46  
% 14.99/6.46  Ordering : KBO
% 14.99/6.46  
% 14.99/6.46  Simplification rules
% 14.99/6.46  ----------------------
% 14.99/6.46  #Subsume      : 1245
% 14.99/6.46  #Demod        : 6712
% 14.99/6.46  #Tautology    : 795
% 14.99/6.46  #SimpNegUnit  : 2285
% 14.99/6.46  #BackRed      : 30
% 14.99/6.46  
% 14.99/6.46  #Partial instantiations: 0
% 14.99/6.46  #Strategies tried      : 1
% 14.99/6.46  
% 14.99/6.46  Timing (in seconds)
% 14.99/6.46  ----------------------
% 14.99/6.46  Preprocessing        : 0.34
% 14.99/6.46  Parsing              : 0.18
% 14.99/6.46  CNF conversion       : 0.03
% 14.99/6.46  Main loop            : 5.33
% 14.99/6.46  Inferencing          : 1.20
% 14.99/6.46  Reduction            : 1.75
% 14.99/6.46  Demodulation         : 1.30
% 14.99/6.46  BG Simplification    : 0.15
% 14.99/6.46  Subsumption          : 2.01
% 14.99/6.46  Abstraction          : 0.25
% 14.99/6.46  MUC search           : 0.00
% 14.99/6.46  Cooper               : 0.00
% 14.99/6.46  Total                : 5.73
% 14.99/6.46  Index Insertion      : 0.00
% 14.99/6.46  Index Deletion       : 0.00
% 14.99/6.46  Index Matching       : 0.00
% 14.99/6.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
