%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:49 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 286 expanded)
%              Number of leaves         :   31 ( 124 expanded)
%              Depth                    :   37
%              Number of atoms          :  327 (1298 expanded)
%              Number of equality atoms :   23 ( 116 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_9_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff(a_2_9_lattice3,type,(
    a_2_9_lattice3: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_168,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( ( r2_hidden(B,C)
                  & r3_lattice3(A,B,C) )
               => k16_lattice3(A,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( B = k16_lattice3(A,C)
            <=> ( r3_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r3_lattice3(A,D,C)
                     => r3_lattices(A,D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & v4_lattice3(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_9_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r3_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_9_lattice3)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r4_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r3_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

tff(f_148,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( r2_hidden(B,C)
                & r4_lattice3(A,B,C) )
             => k15_lattice3(A,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r2_hidden(B,C)
             => ( r3_lattices(A,B,k15_lattice3(A,C))
                & r3_lattices(A,k16_lattice3(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_44,plain,(
    k16_lattice3('#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_56,plain,(
    v10_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_54,plain,(
    v4_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_52,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_46,plain,(
    r3_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_34,plain,(
    ! [A_53,B_65,C_71] :
      ( r3_lattice3(A_53,'#skF_4'(A_53,B_65,C_71),C_71)
      | k16_lattice3(A_53,C_71) = B_65
      | ~ r3_lattice3(A_53,B_65,C_71)
      | ~ m1_subset_1(B_65,u1_struct_0(A_53))
      | ~ l3_lattices(A_53)
      | ~ v4_lattice3(A_53)
      | ~ v10_lattices(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_36,plain,(
    ! [A_53,B_65,C_71] :
      ( m1_subset_1('#skF_4'(A_53,B_65,C_71),u1_struct_0(A_53))
      | k16_lattice3(A_53,C_71) = B_65
      | ~ r3_lattice3(A_53,B_65,C_71)
      | ~ m1_subset_1(B_65,u1_struct_0(A_53))
      | ~ l3_lattices(A_53)
      | ~ v4_lattice3(A_53)
      | ~ v10_lattices(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_20,plain,(
    ! [D_52,B_48,C_49] :
      ( r2_hidden(D_52,a_2_9_lattice3(B_48,C_49))
      | ~ r3_lattice3(B_48,D_52,C_49)
      | ~ m1_subset_1(D_52,u1_struct_0(B_48))
      | ~ l3_lattices(B_48)
      | ~ v4_lattice3(B_48)
      | ~ v10_lattices(B_48)
      | v2_struct_0(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14,plain,(
    ! [A_23,B_35,C_41] :
      ( r2_hidden('#skF_2'(A_23,B_35,C_41),C_41)
      | r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_62,plain,(
    ! [A_101,B_102,C_103] :
      ( '#skF_3'(A_101,B_102,C_103) = A_101
      | ~ r2_hidden(A_101,a_2_9_lattice3(B_102,C_103))
      | ~ l3_lattices(B_102)
      | ~ v4_lattice3(B_102)
      | ~ v10_lattices(B_102)
      | v2_struct_0(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_395,plain,(
    ! [A_196,B_197,B_198,C_199] :
      ( '#skF_3'('#skF_2'(A_196,B_197,a_2_9_lattice3(B_198,C_199)),B_198,C_199) = '#skF_2'(A_196,B_197,a_2_9_lattice3(B_198,C_199))
      | ~ l3_lattices(B_198)
      | ~ v4_lattice3(B_198)
      | ~ v10_lattices(B_198)
      | v2_struct_0(B_198)
      | r4_lattice3(A_196,B_197,a_2_9_lattice3(B_198,C_199))
      | ~ m1_subset_1(B_197,u1_struct_0(A_196))
      | ~ l3_lattices(A_196)
      | v2_struct_0(A_196) ) ),
    inference(resolution,[status(thm)],[c_14,c_62])).

tff(c_22,plain,(
    ! [B_48,A_47,C_49] :
      ( r3_lattice3(B_48,'#skF_3'(A_47,B_48,C_49),C_49)
      | ~ r2_hidden(A_47,a_2_9_lattice3(B_48,C_49))
      | ~ l3_lattices(B_48)
      | ~ v4_lattice3(B_48)
      | ~ v10_lattices(B_48)
      | v2_struct_0(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    ! [A_47,B_48,C_49] :
      ( m1_subset_1('#skF_3'(A_47,B_48,C_49),u1_struct_0(B_48))
      | ~ r2_hidden(A_47,a_2_9_lattice3(B_48,C_49))
      | ~ l3_lattices(B_48)
      | ~ v4_lattice3(B_48)
      | ~ v10_lattices(B_48)
      | v2_struct_0(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_48,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_180,plain,(
    ! [A_153,B_154,D_155,C_156] :
      ( r1_lattices(A_153,B_154,D_155)
      | ~ r2_hidden(D_155,C_156)
      | ~ m1_subset_1(D_155,u1_struct_0(A_153))
      | ~ r3_lattice3(A_153,B_154,C_156)
      | ~ m1_subset_1(B_154,u1_struct_0(A_153))
      | ~ l3_lattices(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_202,plain,(
    ! [A_160,B_161] :
      ( r1_lattices(A_160,B_161,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_160))
      | ~ r3_lattice3(A_160,B_161,'#skF_7')
      | ~ m1_subset_1(B_161,u1_struct_0(A_160))
      | ~ l3_lattices(A_160)
      | v2_struct_0(A_160) ) ),
    inference(resolution,[status(thm)],[c_48,c_180])).

tff(c_204,plain,(
    ! [B_161] :
      ( r1_lattices('#skF_5',B_161,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_161,'#skF_7')
      | ~ m1_subset_1(B_161,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_202])).

tff(c_207,plain,(
    ! [B_161] :
      ( r1_lattices('#skF_5',B_161,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_161,'#skF_7')
      | ~ m1_subset_1(B_161,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_204])).

tff(c_209,plain,(
    ! [B_162] :
      ( r1_lattices('#skF_5',B_162,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_162,'#skF_7')
      | ~ m1_subset_1(B_162,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_207])).

tff(c_217,plain,(
    ! [A_47,C_49] :
      ( r1_lattices('#skF_5','#skF_3'(A_47,'#skF_5',C_49),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_3'(A_47,'#skF_5',C_49),'#skF_7')
      | ~ r2_hidden(A_47,a_2_9_lattice3('#skF_5',C_49))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_209])).

tff(c_239,plain,(
    ! [A_47,C_49] :
      ( r1_lattices('#skF_5','#skF_3'(A_47,'#skF_5',C_49),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_3'(A_47,'#skF_5',C_49),'#skF_7')
      | ~ r2_hidden(A_47,a_2_9_lattice3('#skF_5',C_49))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_217])).

tff(c_257,plain,(
    ! [A_164,C_165] :
      ( r1_lattices('#skF_5','#skF_3'(A_164,'#skF_5',C_165),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_3'(A_164,'#skF_5',C_165),'#skF_7')
      | ~ r2_hidden(A_164,a_2_9_lattice3('#skF_5',C_165)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_239])).

tff(c_264,plain,(
    ! [A_47] :
      ( r1_lattices('#skF_5','#skF_3'(A_47,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_47,a_2_9_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_257])).

tff(c_269,plain,(
    ! [A_47] :
      ( r1_lattices('#skF_5','#skF_3'(A_47,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_47,a_2_9_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_264])).

tff(c_270,plain,(
    ! [A_47] :
      ( r1_lattices('#skF_5','#skF_3'(A_47,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_47,a_2_9_lattice3('#skF_5','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_269])).

tff(c_402,plain,(
    ! [A_196,B_197] :
      ( r1_lattices('#skF_5','#skF_2'(A_196,B_197,a_2_9_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_196,B_197,a_2_9_lattice3('#skF_5','#skF_7')),a_2_9_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | r4_lattice3(A_196,B_197,a_2_9_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_197,u1_struct_0(A_196))
      | ~ l3_lattices(A_196)
      | v2_struct_0(A_196) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_270])).

tff(c_422,plain,(
    ! [A_196,B_197] :
      ( r1_lattices('#skF_5','#skF_2'(A_196,B_197,a_2_9_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_196,B_197,a_2_9_lattice3('#skF_5','#skF_7')),a_2_9_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5')
      | r4_lattice3(A_196,B_197,a_2_9_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_197,u1_struct_0(A_196))
      | ~ l3_lattices(A_196)
      | v2_struct_0(A_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_402])).

tff(c_489,plain,(
    ! [A_205,B_206] :
      ( r1_lattices('#skF_5','#skF_2'(A_205,B_206,a_2_9_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_205,B_206,a_2_9_lattice3('#skF_5','#skF_7')),a_2_9_lattice3('#skF_5','#skF_7'))
      | r4_lattice3(A_205,B_206,a_2_9_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_206,u1_struct_0(A_205))
      | ~ l3_lattices(A_205)
      | v2_struct_0(A_205) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_422])).

tff(c_502,plain,(
    ! [A_207,B_208] :
      ( r1_lattices('#skF_5','#skF_2'(A_207,B_208,a_2_9_lattice3('#skF_5','#skF_7')),'#skF_6')
      | r4_lattice3(A_207,B_208,a_2_9_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_208,u1_struct_0(A_207))
      | ~ l3_lattices(A_207)
      | v2_struct_0(A_207) ) ),
    inference(resolution,[status(thm)],[c_14,c_489])).

tff(c_12,plain,(
    ! [A_23,B_35,C_41] :
      ( ~ r1_lattices(A_23,'#skF_2'(A_23,B_35,C_41),B_35)
      | r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_506,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_9_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_502,c_12])).

tff(c_509,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_9_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_506])).

tff(c_510,plain,(
    r4_lattice3('#skF_5','#skF_6',a_2_9_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_509])).

tff(c_42,plain,(
    ! [A_82,C_88,B_86] :
      ( k15_lattice3(A_82,C_88) = B_86
      | ~ r4_lattice3(A_82,B_86,C_88)
      | ~ r2_hidden(B_86,C_88)
      | ~ m1_subset_1(B_86,u1_struct_0(A_82))
      | ~ l3_lattices(A_82)
      | ~ v4_lattice3(A_82)
      | ~ v10_lattices(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_512,plain,
    ( k15_lattice3('#skF_5',a_2_9_lattice3('#skF_5','#skF_7')) = '#skF_6'
    | ~ r2_hidden('#skF_6',a_2_9_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_510,c_42])).

tff(c_515,plain,
    ( k15_lattice3('#skF_5',a_2_9_lattice3('#skF_5','#skF_7')) = '#skF_6'
    | ~ r2_hidden('#skF_6',a_2_9_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_512])).

tff(c_516,plain,
    ( k15_lattice3('#skF_5',a_2_9_lattice3('#skF_5','#skF_7')) = '#skF_6'
    | ~ r2_hidden('#skF_6',a_2_9_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_515])).

tff(c_517,plain,(
    ~ r2_hidden('#skF_6',a_2_9_lattice3('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_516])).

tff(c_520,plain,
    ( ~ r3_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_517])).

tff(c_523,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_46,c_520])).

tff(c_525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_523])).

tff(c_526,plain,(
    k15_lattice3('#skF_5',a_2_9_lattice3('#skF_5','#skF_7')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_516])).

tff(c_40,plain,(
    ! [A_75,B_79,C_81] :
      ( r3_lattices(A_75,B_79,k15_lattice3(A_75,C_81))
      | ~ r2_hidden(B_79,C_81)
      | ~ m1_subset_1(B_79,u1_struct_0(A_75))
      | ~ l3_lattices(A_75)
      | ~ v4_lattice3(A_75)
      | ~ v10_lattices(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_598,plain,(
    ! [B_79] :
      ( r3_lattices('#skF_5',B_79,'#skF_6')
      | ~ r2_hidden(B_79,a_2_9_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_40])).

tff(c_613,plain,(
    ! [B_79] :
      ( r3_lattices('#skF_5',B_79,'#skF_6')
      | ~ r2_hidden(B_79,a_2_9_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_79,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_598])).

tff(c_619,plain,(
    ! [B_213] :
      ( r3_lattices('#skF_5',B_213,'#skF_6')
      | ~ r2_hidden(B_213,a_2_9_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_213,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_613])).

tff(c_626,plain,(
    ! [D_52] :
      ( r3_lattices('#skF_5',D_52,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_52,'#skF_7')
      | ~ m1_subset_1(D_52,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20,c_619])).

tff(c_640,plain,(
    ! [D_52] :
      ( r3_lattices('#skF_5',D_52,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_52,'#skF_7')
      | ~ m1_subset_1(D_52,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_626])).

tff(c_644,plain,(
    ! [D_214] :
      ( r3_lattices('#skF_5',D_214,'#skF_6')
      | ~ r3_lattice3('#skF_5',D_214,'#skF_7')
      | ~ m1_subset_1(D_214,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_640])).

tff(c_648,plain,(
    ! [B_65,C_71] :
      ( r3_lattices('#skF_5','#skF_4'('#skF_5',B_65,C_71),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'('#skF_5',B_65,C_71),'#skF_7')
      | k16_lattice3('#skF_5',C_71) = B_65
      | ~ r3_lattice3('#skF_5',B_65,C_71)
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_644])).

tff(c_670,plain,(
    ! [B_65,C_71] :
      ( r3_lattices('#skF_5','#skF_4'('#skF_5',B_65,C_71),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'('#skF_5',B_65,C_71),'#skF_7')
      | k16_lattice3('#skF_5',C_71) = B_65
      | ~ r3_lattice3('#skF_5',B_65,C_71)
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_648])).

tff(c_770,plain,(
    ! [B_231,C_232] :
      ( r3_lattices('#skF_5','#skF_4'('#skF_5',B_231,C_232),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'('#skF_5',B_231,C_232),'#skF_7')
      | k16_lattice3('#skF_5',C_232) = B_231
      | ~ r3_lattice3('#skF_5',B_231,C_232)
      | ~ m1_subset_1(B_231,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_670])).

tff(c_32,plain,(
    ! [A_53,B_65,C_71] :
      ( ~ r3_lattices(A_53,'#skF_4'(A_53,B_65,C_71),B_65)
      | k16_lattice3(A_53,C_71) = B_65
      | ~ r3_lattice3(A_53,B_65,C_71)
      | ~ m1_subset_1(B_65,u1_struct_0(A_53))
      | ~ l3_lattices(A_53)
      | ~ v4_lattice3(A_53)
      | ~ v10_lattices(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_774,plain,(
    ! [C_232] :
      ( ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3('#skF_5','#skF_4'('#skF_5','#skF_6',C_232),'#skF_7')
      | k16_lattice3('#skF_5',C_232) = '#skF_6'
      | ~ r3_lattice3('#skF_5','#skF_6',C_232)
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_770,c_32])).

tff(c_777,plain,(
    ! [C_232] :
      ( v2_struct_0('#skF_5')
      | ~ r3_lattice3('#skF_5','#skF_4'('#skF_5','#skF_6',C_232),'#skF_7')
      | k16_lattice3('#skF_5',C_232) = '#skF_6'
      | ~ r3_lattice3('#skF_5','#skF_6',C_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_56,c_54,c_52,c_774])).

tff(c_779,plain,(
    ! [C_233] :
      ( ~ r3_lattice3('#skF_5','#skF_4'('#skF_5','#skF_6',C_233),'#skF_7')
      | k16_lattice3('#skF_5',C_233) = '#skF_6'
      | ~ r3_lattice3('#skF_5','#skF_6',C_233) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_777])).

tff(c_783,plain,
    ( k16_lattice3('#skF_5','#skF_7') = '#skF_6'
    | ~ r3_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_779])).

tff(c_786,plain,
    ( k16_lattice3('#skF_5','#skF_7') = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_46,c_783])).

tff(c_788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_44,c_786])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.51  
% 3.32/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.51  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_9_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 3.32/1.51  
% 3.32/1.51  %Foreground sorts:
% 3.32/1.51  
% 3.32/1.51  
% 3.32/1.51  %Background operators:
% 3.32/1.51  
% 3.32/1.51  
% 3.32/1.51  %Foreground operators:
% 3.32/1.51  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.32/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.32/1.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.32/1.51  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 3.32/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.51  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 3.32/1.51  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 3.32/1.51  tff(a_2_9_lattice3, type, a_2_9_lattice3: ($i * $i) > $i).
% 3.32/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.32/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.32/1.51  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.32/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.32/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.32/1.51  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 3.32/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.32/1.51  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 3.32/1.51  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.32/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.32/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.32/1.51  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 3.32/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.51  
% 3.49/1.53  tff(f_168, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r3_lattice3(A, B, C)) => (k16_lattice3(A, C) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_lattice3)).
% 3.49/1.53  tff(f_110, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 3.49/1.53  tff(f_86, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_9_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r3_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_9_lattice3)).
% 3.49/1.53  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 3.49/1.53  tff(f_43, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 3.49/1.53  tff(f_148, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r4_lattice3(A, B, C)) => (k15_lattice3(A, C) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_lattice3)).
% 3.49/1.53  tff(f_129, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 3.49/1.53  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.49/1.53  tff(c_44, plain, (k16_lattice3('#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.49/1.53  tff(c_56, plain, (v10_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.49/1.53  tff(c_54, plain, (v4_lattice3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.49/1.53  tff(c_52, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.49/1.53  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.49/1.53  tff(c_46, plain, (r3_lattice3('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.49/1.53  tff(c_34, plain, (![A_53, B_65, C_71]: (r3_lattice3(A_53, '#skF_4'(A_53, B_65, C_71), C_71) | k16_lattice3(A_53, C_71)=B_65 | ~r3_lattice3(A_53, B_65, C_71) | ~m1_subset_1(B_65, u1_struct_0(A_53)) | ~l3_lattices(A_53) | ~v4_lattice3(A_53) | ~v10_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.49/1.53  tff(c_36, plain, (![A_53, B_65, C_71]: (m1_subset_1('#skF_4'(A_53, B_65, C_71), u1_struct_0(A_53)) | k16_lattice3(A_53, C_71)=B_65 | ~r3_lattice3(A_53, B_65, C_71) | ~m1_subset_1(B_65, u1_struct_0(A_53)) | ~l3_lattices(A_53) | ~v4_lattice3(A_53) | ~v10_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.49/1.53  tff(c_20, plain, (![D_52, B_48, C_49]: (r2_hidden(D_52, a_2_9_lattice3(B_48, C_49)) | ~r3_lattice3(B_48, D_52, C_49) | ~m1_subset_1(D_52, u1_struct_0(B_48)) | ~l3_lattices(B_48) | ~v4_lattice3(B_48) | ~v10_lattices(B_48) | v2_struct_0(B_48))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.49/1.53  tff(c_14, plain, (![A_23, B_35, C_41]: (r2_hidden('#skF_2'(A_23, B_35, C_41), C_41) | r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.49/1.53  tff(c_62, plain, (![A_101, B_102, C_103]: ('#skF_3'(A_101, B_102, C_103)=A_101 | ~r2_hidden(A_101, a_2_9_lattice3(B_102, C_103)) | ~l3_lattices(B_102) | ~v4_lattice3(B_102) | ~v10_lattices(B_102) | v2_struct_0(B_102))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.49/1.53  tff(c_395, plain, (![A_196, B_197, B_198, C_199]: ('#skF_3'('#skF_2'(A_196, B_197, a_2_9_lattice3(B_198, C_199)), B_198, C_199)='#skF_2'(A_196, B_197, a_2_9_lattice3(B_198, C_199)) | ~l3_lattices(B_198) | ~v4_lattice3(B_198) | ~v10_lattices(B_198) | v2_struct_0(B_198) | r4_lattice3(A_196, B_197, a_2_9_lattice3(B_198, C_199)) | ~m1_subset_1(B_197, u1_struct_0(A_196)) | ~l3_lattices(A_196) | v2_struct_0(A_196))), inference(resolution, [status(thm)], [c_14, c_62])).
% 3.49/1.53  tff(c_22, plain, (![B_48, A_47, C_49]: (r3_lattice3(B_48, '#skF_3'(A_47, B_48, C_49), C_49) | ~r2_hidden(A_47, a_2_9_lattice3(B_48, C_49)) | ~l3_lattices(B_48) | ~v4_lattice3(B_48) | ~v10_lattices(B_48) | v2_struct_0(B_48))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.49/1.53  tff(c_26, plain, (![A_47, B_48, C_49]: (m1_subset_1('#skF_3'(A_47, B_48, C_49), u1_struct_0(B_48)) | ~r2_hidden(A_47, a_2_9_lattice3(B_48, C_49)) | ~l3_lattices(B_48) | ~v4_lattice3(B_48) | ~v10_lattices(B_48) | v2_struct_0(B_48))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.49/1.53  tff(c_48, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_168])).
% 3.49/1.53  tff(c_180, plain, (![A_153, B_154, D_155, C_156]: (r1_lattices(A_153, B_154, D_155) | ~r2_hidden(D_155, C_156) | ~m1_subset_1(D_155, u1_struct_0(A_153)) | ~r3_lattice3(A_153, B_154, C_156) | ~m1_subset_1(B_154, u1_struct_0(A_153)) | ~l3_lattices(A_153) | v2_struct_0(A_153))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.49/1.53  tff(c_202, plain, (![A_160, B_161]: (r1_lattices(A_160, B_161, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0(A_160)) | ~r3_lattice3(A_160, B_161, '#skF_7') | ~m1_subset_1(B_161, u1_struct_0(A_160)) | ~l3_lattices(A_160) | v2_struct_0(A_160))), inference(resolution, [status(thm)], [c_48, c_180])).
% 3.49/1.53  tff(c_204, plain, (![B_161]: (r1_lattices('#skF_5', B_161, '#skF_6') | ~r3_lattice3('#skF_5', B_161, '#skF_7') | ~m1_subset_1(B_161, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_202])).
% 3.49/1.53  tff(c_207, plain, (![B_161]: (r1_lattices('#skF_5', B_161, '#skF_6') | ~r3_lattice3('#skF_5', B_161, '#skF_7') | ~m1_subset_1(B_161, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_204])).
% 3.49/1.53  tff(c_209, plain, (![B_162]: (r1_lattices('#skF_5', B_162, '#skF_6') | ~r3_lattice3('#skF_5', B_162, '#skF_7') | ~m1_subset_1(B_162, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_207])).
% 3.49/1.53  tff(c_217, plain, (![A_47, C_49]: (r1_lattices('#skF_5', '#skF_3'(A_47, '#skF_5', C_49), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_3'(A_47, '#skF_5', C_49), '#skF_7') | ~r2_hidden(A_47, a_2_9_lattice3('#skF_5', C_49)) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_26, c_209])).
% 3.49/1.53  tff(c_239, plain, (![A_47, C_49]: (r1_lattices('#skF_5', '#skF_3'(A_47, '#skF_5', C_49), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_3'(A_47, '#skF_5', C_49), '#skF_7') | ~r2_hidden(A_47, a_2_9_lattice3('#skF_5', C_49)) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_217])).
% 3.49/1.53  tff(c_257, plain, (![A_164, C_165]: (r1_lattices('#skF_5', '#skF_3'(A_164, '#skF_5', C_165), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_3'(A_164, '#skF_5', C_165), '#skF_7') | ~r2_hidden(A_164, a_2_9_lattice3('#skF_5', C_165)))), inference(negUnitSimplification, [status(thm)], [c_58, c_239])).
% 3.49/1.53  tff(c_264, plain, (![A_47]: (r1_lattices('#skF_5', '#skF_3'(A_47, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_47, a_2_9_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_22, c_257])).
% 3.49/1.53  tff(c_269, plain, (![A_47]: (r1_lattices('#skF_5', '#skF_3'(A_47, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_47, a_2_9_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_264])).
% 3.49/1.53  tff(c_270, plain, (![A_47]: (r1_lattices('#skF_5', '#skF_3'(A_47, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_47, a_2_9_lattice3('#skF_5', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_58, c_269])).
% 3.49/1.53  tff(c_402, plain, (![A_196, B_197]: (r1_lattices('#skF_5', '#skF_2'(A_196, B_197, a_2_9_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_196, B_197, a_2_9_lattice3('#skF_5', '#skF_7')), a_2_9_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | r4_lattice3(A_196, B_197, a_2_9_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_197, u1_struct_0(A_196)) | ~l3_lattices(A_196) | v2_struct_0(A_196))), inference(superposition, [status(thm), theory('equality')], [c_395, c_270])).
% 3.49/1.53  tff(c_422, plain, (![A_196, B_197]: (r1_lattices('#skF_5', '#skF_2'(A_196, B_197, a_2_9_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_196, B_197, a_2_9_lattice3('#skF_5', '#skF_7')), a_2_9_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5') | r4_lattice3(A_196, B_197, a_2_9_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_197, u1_struct_0(A_196)) | ~l3_lattices(A_196) | v2_struct_0(A_196))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_402])).
% 3.49/1.53  tff(c_489, plain, (![A_205, B_206]: (r1_lattices('#skF_5', '#skF_2'(A_205, B_206, a_2_9_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_205, B_206, a_2_9_lattice3('#skF_5', '#skF_7')), a_2_9_lattice3('#skF_5', '#skF_7')) | r4_lattice3(A_205, B_206, a_2_9_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_206, u1_struct_0(A_205)) | ~l3_lattices(A_205) | v2_struct_0(A_205))), inference(negUnitSimplification, [status(thm)], [c_58, c_422])).
% 3.49/1.53  tff(c_502, plain, (![A_207, B_208]: (r1_lattices('#skF_5', '#skF_2'(A_207, B_208, a_2_9_lattice3('#skF_5', '#skF_7')), '#skF_6') | r4_lattice3(A_207, B_208, a_2_9_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_208, u1_struct_0(A_207)) | ~l3_lattices(A_207) | v2_struct_0(A_207))), inference(resolution, [status(thm)], [c_14, c_489])).
% 3.49/1.53  tff(c_12, plain, (![A_23, B_35, C_41]: (~r1_lattices(A_23, '#skF_2'(A_23, B_35, C_41), B_35) | r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.49/1.53  tff(c_506, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_9_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_502, c_12])).
% 3.49/1.53  tff(c_509, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_9_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_506])).
% 3.49/1.53  tff(c_510, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_9_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_58, c_509])).
% 3.49/1.53  tff(c_42, plain, (![A_82, C_88, B_86]: (k15_lattice3(A_82, C_88)=B_86 | ~r4_lattice3(A_82, B_86, C_88) | ~r2_hidden(B_86, C_88) | ~m1_subset_1(B_86, u1_struct_0(A_82)) | ~l3_lattices(A_82) | ~v4_lattice3(A_82) | ~v10_lattices(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.49/1.53  tff(c_512, plain, (k15_lattice3('#skF_5', a_2_9_lattice3('#skF_5', '#skF_7'))='#skF_6' | ~r2_hidden('#skF_6', a_2_9_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_510, c_42])).
% 3.49/1.53  tff(c_515, plain, (k15_lattice3('#skF_5', a_2_9_lattice3('#skF_5', '#skF_7'))='#skF_6' | ~r2_hidden('#skF_6', a_2_9_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_512])).
% 3.49/1.53  tff(c_516, plain, (k15_lattice3('#skF_5', a_2_9_lattice3('#skF_5', '#skF_7'))='#skF_6' | ~r2_hidden('#skF_6', a_2_9_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_58, c_515])).
% 3.49/1.53  tff(c_517, plain, (~r2_hidden('#skF_6', a_2_9_lattice3('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_516])).
% 3.49/1.53  tff(c_520, plain, (~r3_lattice3('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_20, c_517])).
% 3.49/1.53  tff(c_523, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_46, c_520])).
% 3.49/1.53  tff(c_525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_523])).
% 3.49/1.53  tff(c_526, plain, (k15_lattice3('#skF_5', a_2_9_lattice3('#skF_5', '#skF_7'))='#skF_6'), inference(splitRight, [status(thm)], [c_516])).
% 3.49/1.53  tff(c_40, plain, (![A_75, B_79, C_81]: (r3_lattices(A_75, B_79, k15_lattice3(A_75, C_81)) | ~r2_hidden(B_79, C_81) | ~m1_subset_1(B_79, u1_struct_0(A_75)) | ~l3_lattices(A_75) | ~v4_lattice3(A_75) | ~v10_lattices(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.49/1.53  tff(c_598, plain, (![B_79]: (r3_lattices('#skF_5', B_79, '#skF_6') | ~r2_hidden(B_79, a_2_9_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_79, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_526, c_40])).
% 3.49/1.53  tff(c_613, plain, (![B_79]: (r3_lattices('#skF_5', B_79, '#skF_6') | ~r2_hidden(B_79, a_2_9_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_79, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_598])).
% 3.49/1.53  tff(c_619, plain, (![B_213]: (r3_lattices('#skF_5', B_213, '#skF_6') | ~r2_hidden(B_213, a_2_9_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_213, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_613])).
% 3.49/1.53  tff(c_626, plain, (![D_52]: (r3_lattices('#skF_5', D_52, '#skF_6') | ~r3_lattice3('#skF_5', D_52, '#skF_7') | ~m1_subset_1(D_52, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_619])).
% 3.49/1.53  tff(c_640, plain, (![D_52]: (r3_lattices('#skF_5', D_52, '#skF_6') | ~r3_lattice3('#skF_5', D_52, '#skF_7') | ~m1_subset_1(D_52, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_626])).
% 3.49/1.53  tff(c_644, plain, (![D_214]: (r3_lattices('#skF_5', D_214, '#skF_6') | ~r3_lattice3('#skF_5', D_214, '#skF_7') | ~m1_subset_1(D_214, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_640])).
% 3.49/1.53  tff(c_648, plain, (![B_65, C_71]: (r3_lattices('#skF_5', '#skF_4'('#skF_5', B_65, C_71), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'('#skF_5', B_65, C_71), '#skF_7') | k16_lattice3('#skF_5', C_71)=B_65 | ~r3_lattice3('#skF_5', B_65, C_71) | ~m1_subset_1(B_65, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_644])).
% 3.49/1.53  tff(c_670, plain, (![B_65, C_71]: (r3_lattices('#skF_5', '#skF_4'('#skF_5', B_65, C_71), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'('#skF_5', B_65, C_71), '#skF_7') | k16_lattice3('#skF_5', C_71)=B_65 | ~r3_lattice3('#skF_5', B_65, C_71) | ~m1_subset_1(B_65, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_648])).
% 3.49/1.53  tff(c_770, plain, (![B_231, C_232]: (r3_lattices('#skF_5', '#skF_4'('#skF_5', B_231, C_232), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'('#skF_5', B_231, C_232), '#skF_7') | k16_lattice3('#skF_5', C_232)=B_231 | ~r3_lattice3('#skF_5', B_231, C_232) | ~m1_subset_1(B_231, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_670])).
% 3.49/1.53  tff(c_32, plain, (![A_53, B_65, C_71]: (~r3_lattices(A_53, '#skF_4'(A_53, B_65, C_71), B_65) | k16_lattice3(A_53, C_71)=B_65 | ~r3_lattice3(A_53, B_65, C_71) | ~m1_subset_1(B_65, u1_struct_0(A_53)) | ~l3_lattices(A_53) | ~v4_lattice3(A_53) | ~v10_lattices(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.49/1.53  tff(c_774, plain, (![C_232]: (~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_232), '#skF_7') | k16_lattice3('#skF_5', C_232)='#skF_6' | ~r3_lattice3('#skF_5', '#skF_6', C_232) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_770, c_32])).
% 3.49/1.53  tff(c_777, plain, (![C_232]: (v2_struct_0('#skF_5') | ~r3_lattice3('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_232), '#skF_7') | k16_lattice3('#skF_5', C_232)='#skF_6' | ~r3_lattice3('#skF_5', '#skF_6', C_232))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_56, c_54, c_52, c_774])).
% 3.49/1.53  tff(c_779, plain, (![C_233]: (~r3_lattice3('#skF_5', '#skF_4'('#skF_5', '#skF_6', C_233), '#skF_7') | k16_lattice3('#skF_5', C_233)='#skF_6' | ~r3_lattice3('#skF_5', '#skF_6', C_233))), inference(negUnitSimplification, [status(thm)], [c_58, c_777])).
% 3.49/1.53  tff(c_783, plain, (k16_lattice3('#skF_5', '#skF_7')='#skF_6' | ~r3_lattice3('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_779])).
% 3.49/1.53  tff(c_786, plain, (k16_lattice3('#skF_5', '#skF_7')='#skF_6' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_46, c_783])).
% 3.49/1.53  tff(c_788, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_44, c_786])).
% 3.49/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.53  
% 3.49/1.53  Inference rules
% 3.49/1.53  ----------------------
% 3.49/1.53  #Ref     : 0
% 3.49/1.53  #Sup     : 127
% 3.49/1.53  #Fact    : 0
% 3.49/1.53  #Define  : 0
% 3.49/1.53  #Split   : 2
% 3.49/1.53  #Chain   : 0
% 3.49/1.53  #Close   : 0
% 3.49/1.53  
% 3.49/1.53  Ordering : KBO
% 3.49/1.53  
% 3.49/1.53  Simplification rules
% 3.49/1.53  ----------------------
% 3.49/1.53  #Subsume      : 7
% 3.49/1.53  #Demod        : 195
% 3.49/1.53  #Tautology    : 32
% 3.49/1.53  #SimpNegUnit  : 55
% 3.49/1.53  #BackRed      : 0
% 3.49/1.53  
% 3.49/1.53  #Partial instantiations: 0
% 3.49/1.53  #Strategies tried      : 1
% 3.49/1.53  
% 3.49/1.53  Timing (in seconds)
% 3.49/1.53  ----------------------
% 3.49/1.54  Preprocessing        : 0.35
% 3.49/1.54  Parsing              : 0.19
% 3.49/1.54  CNF conversion       : 0.03
% 3.49/1.54  Main loop            : 0.41
% 3.49/1.54  Inferencing          : 0.17
% 3.49/1.54  Reduction            : 0.11
% 3.49/1.54  Demodulation         : 0.08
% 3.49/1.54  BG Simplification    : 0.03
% 3.49/1.54  Subsumption          : 0.08
% 3.49/1.54  Abstraction          : 0.02
% 3.49/1.54  MUC search           : 0.00
% 3.49/1.54  Cooper               : 0.00
% 3.49/1.54  Total                : 0.80
% 3.49/1.54  Index Insertion      : 0.00
% 3.49/1.54  Index Deletion       : 0.00
% 3.49/1.54  Index Matching       : 0.00
% 3.49/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
