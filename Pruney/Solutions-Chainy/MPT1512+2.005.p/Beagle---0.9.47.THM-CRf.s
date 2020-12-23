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
% DateTime   : Thu Dec  3 10:24:50 EST 2020

% Result     : Theorem 8.84s
% Output     : CNFRefutation 8.84s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 373 expanded)
%              Number of leaves         :   36 ( 145 expanded)
%              Depth                    :   14
%              Number of atoms          :  531 (1546 expanded)
%              Number of equality atoms :    6 (  21 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff(a_2_2_lattice3,type,(
    a_2_2_lattice3: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_170,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B,C] :
            ( r1_tarski(B,C)
           => ( r3_lattices(A,k15_lattice3(A,B),k15_lattice3(A,C))
              & r3_lattices(A,k16_lattice3(A,C),k16_lattice3(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k16_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

tff(f_124,axiom,(
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

tff(f_153,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r3_lattice3(A,B,C)
             => r3_lattices(A,B,k16_lattice3(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice3)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & v4_lattice3(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_2_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r4_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

tff(f_68,axiom,(
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

tff(f_136,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] : k15_lattice3(A,B) = k16_lattice3(A,a_2_2_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

tff(f_50,axiom,(
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

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_96,B_97] :
      ( ~ r2_hidden('#skF_1'(A_96,B_97),B_97)
      | r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_54,plain,(
    l3_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_58,plain,(
    v10_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_56,plain,(
    v4_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_26,plain,(
    ! [A_52,B_53] :
      ( m1_subset_1(k16_lattice3(A_52,B_53),u1_struct_0(A_52))
      | ~ l3_lattices(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4458,plain,(
    ! [A_1095,C_1096] :
      ( r3_lattice3(A_1095,k16_lattice3(A_1095,C_1096),C_1096)
      | ~ m1_subset_1(k16_lattice3(A_1095,C_1096),u1_struct_0(A_1095))
      | ~ l3_lattices(A_1095)
      | ~ v4_lattice3(A_1095)
      | ~ v10_lattices(A_1095)
      | v2_struct_0(A_1095) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4463,plain,(
    ! [A_52,B_53] :
      ( r3_lattice3(A_52,k16_lattice3(A_52,B_53),B_53)
      | ~ v4_lattice3(A_52)
      | ~ v10_lattices(A_52)
      | ~ l3_lattices(A_52)
      | v2_struct_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_26,c_4458])).

tff(c_4499,plain,(
    ! [A_1110,B_1111,C_1112] :
      ( r3_lattices(A_1110,B_1111,k16_lattice3(A_1110,C_1112))
      | ~ r3_lattice3(A_1110,B_1111,C_1112)
      | ~ m1_subset_1(B_1111,u1_struct_0(A_1110))
      | ~ l3_lattices(A_1110)
      | ~ v4_lattice3(A_1110)
      | ~ v10_lattices(A_1110)
      | v2_struct_0(A_1110) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_69,plain,(
    ! [C_99,B_100,A_101] :
      ( r2_hidden(C_99,B_100)
      | ~ r2_hidden(C_99,A_101)
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [A_1,B_2,B_100] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_100)
      | ~ r1_tarski(A_1,B_100)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_141,plain,(
    ! [A_127,B_128,C_129] :
      ( '#skF_4'(A_127,B_128,C_129) = A_127
      | ~ r2_hidden(A_127,a_2_2_lattice3(B_128,C_129))
      | ~ l3_lattices(B_128)
      | ~ v4_lattice3(B_128)
      | ~ v10_lattices(B_128)
      | v2_struct_0(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_364,plain,(
    ! [B_228,C_229,B_230] :
      ( '#skF_4'('#skF_1'(a_2_2_lattice3(B_228,C_229),B_230),B_228,C_229) = '#skF_1'(a_2_2_lattice3(B_228,C_229),B_230)
      | ~ l3_lattices(B_228)
      | ~ v4_lattice3(B_228)
      | ~ v10_lattices(B_228)
      | v2_struct_0(B_228)
      | r1_tarski(a_2_2_lattice3(B_228,C_229),B_230) ) ),
    inference(resolution,[status(thm)],[c_6,c_141])).

tff(c_34,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1('#skF_4'(A_54,B_55,C_56),u1_struct_0(B_55))
      | ~ r2_hidden(A_54,a_2_2_lattice3(B_55,C_56))
      | ~ l3_lattices(B_55)
      | ~ v4_lattice3(B_55)
      | ~ v10_lattices(B_55)
      | v2_struct_0(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1178,plain,(
    ! [B_459,C_460,B_461] :
      ( m1_subset_1('#skF_1'(a_2_2_lattice3(B_459,C_460),B_461),u1_struct_0(B_459))
      | ~ r2_hidden('#skF_1'(a_2_2_lattice3(B_459,C_460),B_461),a_2_2_lattice3(B_459,C_460))
      | ~ l3_lattices(B_459)
      | ~ v4_lattice3(B_459)
      | ~ v10_lattices(B_459)
      | v2_struct_0(B_459)
      | ~ l3_lattices(B_459)
      | ~ v4_lattice3(B_459)
      | ~ v10_lattices(B_459)
      | v2_struct_0(B_459)
      | r1_tarski(a_2_2_lattice3(B_459,C_460),B_461) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_34])).

tff(c_1190,plain,(
    ! [B_459,C_460,B_2] :
      ( m1_subset_1('#skF_1'(a_2_2_lattice3(B_459,C_460),B_2),u1_struct_0(B_459))
      | ~ l3_lattices(B_459)
      | ~ v4_lattice3(B_459)
      | ~ v10_lattices(B_459)
      | v2_struct_0(B_459)
      | ~ r1_tarski(a_2_2_lattice3(B_459,C_460),a_2_2_lattice3(B_459,C_460))
      | r1_tarski(a_2_2_lattice3(B_459,C_460),B_2) ) ),
    inference(resolution,[status(thm)],[c_72,c_1178])).

tff(c_1199,plain,(
    ! [B_459,C_460,B_2] :
      ( m1_subset_1('#skF_1'(a_2_2_lattice3(B_459,C_460),B_2),u1_struct_0(B_459))
      | ~ l3_lattices(B_459)
      | ~ v4_lattice3(B_459)
      | ~ v10_lattices(B_459)
      | v2_struct_0(B_459)
      | r1_tarski(a_2_2_lattice3(B_459,C_460),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_1190])).

tff(c_30,plain,(
    ! [B_55,A_54,C_56] :
      ( r4_lattice3(B_55,'#skF_4'(A_54,B_55,C_56),C_56)
      | ~ r2_hidden(A_54,a_2_2_lattice3(B_55,C_56))
      | ~ l3_lattices(B_55)
      | ~ v4_lattice3(B_55)
      | ~ v10_lattices(B_55)
      | v2_struct_0(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1127,plain,(
    ! [B_450,C_451,B_452] :
      ( r4_lattice3(B_450,'#skF_1'(a_2_2_lattice3(B_450,C_451),B_452),C_451)
      | ~ r2_hidden('#skF_1'(a_2_2_lattice3(B_450,C_451),B_452),a_2_2_lattice3(B_450,C_451))
      | ~ l3_lattices(B_450)
      | ~ v4_lattice3(B_450)
      | ~ v10_lattices(B_450)
      | v2_struct_0(B_450)
      | ~ l3_lattices(B_450)
      | ~ v4_lattice3(B_450)
      | ~ v10_lattices(B_450)
      | v2_struct_0(B_450)
      | r1_tarski(a_2_2_lattice3(B_450,C_451),B_452) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_30])).

tff(c_1139,plain,(
    ! [B_450,C_451,B_2] :
      ( r4_lattice3(B_450,'#skF_1'(a_2_2_lattice3(B_450,C_451),B_2),C_451)
      | ~ l3_lattices(B_450)
      | ~ v4_lattice3(B_450)
      | ~ v10_lattices(B_450)
      | v2_struct_0(B_450)
      | ~ r1_tarski(a_2_2_lattice3(B_450,C_451),a_2_2_lattice3(B_450,C_451))
      | r1_tarski(a_2_2_lattice3(B_450,C_451),B_2) ) ),
    inference(resolution,[status(thm)],[c_72,c_1127])).

tff(c_1148,plain,(
    ! [B_450,C_451,B_2] :
      ( r4_lattice3(B_450,'#skF_1'(a_2_2_lattice3(B_450,C_451),B_2),C_451)
      | ~ l3_lattices(B_450)
      | ~ v4_lattice3(B_450)
      | ~ v10_lattices(B_450)
      | v2_struct_0(B_450)
      | r1_tarski(a_2_2_lattice3(B_450,C_451),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_1139])).

tff(c_22,plain,(
    ! [A_28,B_40,C_46] :
      ( m1_subset_1('#skF_3'(A_28,B_40,C_46),u1_struct_0(A_28))
      | r4_lattice3(A_28,B_40,C_46)
      | ~ m1_subset_1(B_40,u1_struct_0(A_28))
      | ~ l3_lattices(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_52,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_157,plain,(
    ! [A_130,B_131,C_132] :
      ( r2_hidden('#skF_3'(A_130,B_131,C_132),C_132)
      | r4_lattice3(A_130,B_131,C_132)
      | ~ m1_subset_1(B_131,u1_struct_0(A_130))
      | ~ l3_lattices(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_218,plain,(
    ! [A_172,B_173,C_174,B_175] :
      ( r2_hidden('#skF_3'(A_172,B_173,C_174),B_175)
      | ~ r1_tarski(C_174,B_175)
      | r4_lattice3(A_172,B_173,C_174)
      | ~ m1_subset_1(B_173,u1_struct_0(A_172))
      | ~ l3_lattices(A_172)
      | v2_struct_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_312,plain,(
    ! [B_208,B_212,C_211,B_209,A_210] :
      ( r2_hidden('#skF_3'(A_210,B_208,C_211),B_209)
      | ~ r1_tarski(B_212,B_209)
      | ~ r1_tarski(C_211,B_212)
      | r4_lattice3(A_210,B_208,C_211)
      | ~ m1_subset_1(B_208,u1_struct_0(A_210))
      | ~ l3_lattices(A_210)
      | v2_struct_0(A_210) ) ),
    inference(resolution,[status(thm)],[c_218,c_2])).

tff(c_319,plain,(
    ! [A_213,B_214,C_215] :
      ( r2_hidden('#skF_3'(A_213,B_214,C_215),'#skF_8')
      | ~ r1_tarski(C_215,'#skF_7')
      | r4_lattice3(A_213,B_214,C_215)
      | ~ m1_subset_1(B_214,u1_struct_0(A_213))
      | ~ l3_lattices(A_213)
      | v2_struct_0(A_213) ) ),
    inference(resolution,[status(thm)],[c_52,c_312])).

tff(c_16,plain,(
    ! [A_28,D_49,B_40,C_46] :
      ( r1_lattices(A_28,D_49,B_40)
      | ~ r2_hidden(D_49,C_46)
      | ~ m1_subset_1(D_49,u1_struct_0(A_28))
      | ~ r4_lattice3(A_28,B_40,C_46)
      | ~ m1_subset_1(B_40,u1_struct_0(A_28))
      | ~ l3_lattices(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3380,plain,(
    ! [B_964,A_961,C_965,A_963,B_962] :
      ( r1_lattices(A_963,'#skF_3'(A_961,B_964,C_965),B_962)
      | ~ m1_subset_1('#skF_3'(A_961,B_964,C_965),u1_struct_0(A_963))
      | ~ r4_lattice3(A_963,B_962,'#skF_8')
      | ~ m1_subset_1(B_962,u1_struct_0(A_963))
      | ~ l3_lattices(A_963)
      | v2_struct_0(A_963)
      | ~ r1_tarski(C_965,'#skF_7')
      | r4_lattice3(A_961,B_964,C_965)
      | ~ m1_subset_1(B_964,u1_struct_0(A_961))
      | ~ l3_lattices(A_961)
      | v2_struct_0(A_961) ) ),
    inference(resolution,[status(thm)],[c_319,c_16])).

tff(c_3387,plain,(
    ! [A_966,B_967,C_968,B_969] :
      ( r1_lattices(A_966,'#skF_3'(A_966,B_967,C_968),B_969)
      | ~ r4_lattice3(A_966,B_969,'#skF_8')
      | ~ m1_subset_1(B_969,u1_struct_0(A_966))
      | ~ r1_tarski(C_968,'#skF_7')
      | r4_lattice3(A_966,B_967,C_968)
      | ~ m1_subset_1(B_967,u1_struct_0(A_966))
      | ~ l3_lattices(A_966)
      | v2_struct_0(A_966) ) ),
    inference(resolution,[status(thm)],[c_22,c_3380])).

tff(c_18,plain,(
    ! [A_28,B_40,C_46] :
      ( ~ r1_lattices(A_28,'#skF_3'(A_28,B_40,C_46),B_40)
      | r4_lattice3(A_28,B_40,C_46)
      | ~ m1_subset_1(B_40,u1_struct_0(A_28))
      | ~ l3_lattices(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3398,plain,(
    ! [A_970,B_971,C_972] :
      ( ~ r4_lattice3(A_970,B_971,'#skF_8')
      | ~ r1_tarski(C_972,'#skF_7')
      | r4_lattice3(A_970,B_971,C_972)
      | ~ m1_subset_1(B_971,u1_struct_0(A_970))
      | ~ l3_lattices(A_970)
      | v2_struct_0(A_970) ) ),
    inference(resolution,[status(thm)],[c_3387,c_18])).

tff(c_4094,plain,(
    ! [B_1022,C_1023,B_1024,C_1025] :
      ( ~ r4_lattice3(B_1022,'#skF_1'(a_2_2_lattice3(B_1022,C_1023),B_1024),'#skF_8')
      | ~ r1_tarski(C_1025,'#skF_7')
      | r4_lattice3(B_1022,'#skF_1'(a_2_2_lattice3(B_1022,C_1023),B_1024),C_1025)
      | ~ l3_lattices(B_1022)
      | ~ v4_lattice3(B_1022)
      | ~ v10_lattices(B_1022)
      | v2_struct_0(B_1022)
      | r1_tarski(a_2_2_lattice3(B_1022,C_1023),B_1024) ) ),
    inference(resolution,[status(thm)],[c_1199,c_3398])).

tff(c_4099,plain,(
    ! [C_1026,B_1027,B_1028] :
      ( ~ r1_tarski(C_1026,'#skF_7')
      | r4_lattice3(B_1027,'#skF_1'(a_2_2_lattice3(B_1027,'#skF_8'),B_1028),C_1026)
      | ~ l3_lattices(B_1027)
      | ~ v4_lattice3(B_1027)
      | ~ v10_lattices(B_1027)
      | v2_struct_0(B_1027)
      | r1_tarski(a_2_2_lattice3(B_1027,'#skF_8'),B_1028) ) ),
    inference(resolution,[status(thm)],[c_1148,c_4094])).

tff(c_192,plain,(
    ! [D_162,B_163,C_164] :
      ( r2_hidden(D_162,a_2_2_lattice3(B_163,C_164))
      | ~ r4_lattice3(B_163,D_162,C_164)
      | ~ m1_subset_1(D_162,u1_struct_0(B_163))
      | ~ l3_lattices(B_163)
      | ~ v4_lattice3(B_163)
      | ~ v10_lattices(B_163)
      | v2_struct_0(B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_204,plain,(
    ! [A_1,B_163,C_164] :
      ( r1_tarski(A_1,a_2_2_lattice3(B_163,C_164))
      | ~ r4_lattice3(B_163,'#skF_1'(A_1,a_2_2_lattice3(B_163,C_164)),C_164)
      | ~ m1_subset_1('#skF_1'(A_1,a_2_2_lattice3(B_163,C_164)),u1_struct_0(B_163))
      | ~ l3_lattices(B_163)
      | ~ v4_lattice3(B_163)
      | ~ v10_lattices(B_163)
      | v2_struct_0(B_163) ) ),
    inference(resolution,[status(thm)],[c_192,c_4])).

tff(c_4236,plain,(
    ! [B_1035,C_1036] :
      ( ~ m1_subset_1('#skF_1'(a_2_2_lattice3(B_1035,'#skF_8'),a_2_2_lattice3(B_1035,C_1036)),u1_struct_0(B_1035))
      | ~ r1_tarski(C_1036,'#skF_7')
      | ~ l3_lattices(B_1035)
      | ~ v4_lattice3(B_1035)
      | ~ v10_lattices(B_1035)
      | v2_struct_0(B_1035)
      | r1_tarski(a_2_2_lattice3(B_1035,'#skF_8'),a_2_2_lattice3(B_1035,C_1036)) ) ),
    inference(resolution,[status(thm)],[c_4099,c_204])).

tff(c_4242,plain,(
    ! [C_1037,B_1038] :
      ( ~ r1_tarski(C_1037,'#skF_7')
      | ~ l3_lattices(B_1038)
      | ~ v4_lattice3(B_1038)
      | ~ v10_lattices(B_1038)
      | v2_struct_0(B_1038)
      | r1_tarski(a_2_2_lattice3(B_1038,'#skF_8'),a_2_2_lattice3(B_1038,C_1037)) ) ),
    inference(resolution,[status(thm)],[c_1199,c_4236])).

tff(c_46,plain,(
    ! [A_82,B_84] :
      ( k16_lattice3(A_82,a_2_2_lattice3(A_82,B_84)) = k15_lattice3(A_82,B_84)
      | ~ l3_lattices(A_82)
      | ~ v4_lattice3(A_82)
      | ~ v10_lattices(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_182,plain,(
    ! [A_158,C_159] :
      ( r3_lattice3(A_158,k16_lattice3(A_158,C_159),C_159)
      | ~ m1_subset_1(k16_lattice3(A_158,C_159),u1_struct_0(A_158))
      | ~ l3_lattices(A_158)
      | ~ v4_lattice3(A_158)
      | ~ v10_lattices(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_187,plain,(
    ! [A_52,B_53] :
      ( r3_lattice3(A_52,k16_lattice3(A_52,B_53),B_53)
      | ~ v4_lattice3(A_52)
      | ~ v10_lattices(A_52)
      | ~ l3_lattices(A_52)
      | v2_struct_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_26,c_182])).

tff(c_14,plain,(
    ! [A_6,B_18,C_24] :
      ( m1_subset_1('#skF_2'(A_6,B_18,C_24),u1_struct_0(A_6))
      | r3_lattice3(A_6,B_18,C_24)
      | ~ m1_subset_1(B_18,u1_struct_0(A_6))
      | ~ l3_lattices(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_166,plain,(
    ! [A_133,B_134,C_135] :
      ( r2_hidden('#skF_2'(A_133,B_134,C_135),C_135)
      | r3_lattice3(A_133,B_134,C_135)
      | ~ m1_subset_1(B_134,u1_struct_0(A_133))
      | ~ l3_lattices(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_174,plain,(
    ! [A_133,B_134,C_135,B_2] :
      ( r2_hidden('#skF_2'(A_133,B_134,C_135),B_2)
      | ~ r1_tarski(C_135,B_2)
      | r3_lattice3(A_133,B_134,C_135)
      | ~ m1_subset_1(B_134,u1_struct_0(A_133))
      | ~ l3_lattices(A_133)
      | v2_struct_0(A_133) ) ),
    inference(resolution,[status(thm)],[c_166,c_2])).

tff(c_231,plain,(
    ! [A_179,B_180,D_181,C_182] :
      ( r1_lattices(A_179,B_180,D_181)
      | ~ r2_hidden(D_181,C_182)
      | ~ m1_subset_1(D_181,u1_struct_0(A_179))
      | ~ r3_lattice3(A_179,B_180,C_182)
      | ~ m1_subset_1(B_180,u1_struct_0(A_179))
      | ~ l3_lattices(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1706,plain,(
    ! [C_580,B_584,A_579,B_581,B_582,A_583] :
      ( r1_lattices(A_583,B_581,'#skF_2'(A_579,B_582,C_580))
      | ~ m1_subset_1('#skF_2'(A_579,B_582,C_580),u1_struct_0(A_583))
      | ~ r3_lattice3(A_583,B_581,B_584)
      | ~ m1_subset_1(B_581,u1_struct_0(A_583))
      | ~ l3_lattices(A_583)
      | v2_struct_0(A_583)
      | ~ r1_tarski(C_580,B_584)
      | r3_lattice3(A_579,B_582,C_580)
      | ~ m1_subset_1(B_582,u1_struct_0(A_579))
      | ~ l3_lattices(A_579)
      | v2_struct_0(A_579) ) ),
    inference(resolution,[status(thm)],[c_174,c_231])).

tff(c_1764,plain,(
    ! [B_590,B_591,B_592,C_589,A_593] :
      ( r1_lattices(A_593,B_592,'#skF_2'(A_593,B_591,C_589))
      | ~ r3_lattice3(A_593,B_592,B_590)
      | ~ m1_subset_1(B_592,u1_struct_0(A_593))
      | ~ r1_tarski(C_589,B_590)
      | r3_lattice3(A_593,B_591,C_589)
      | ~ m1_subset_1(B_591,u1_struct_0(A_593))
      | ~ l3_lattices(A_593)
      | v2_struct_0(A_593) ) ),
    inference(resolution,[status(thm)],[c_14,c_1706])).

tff(c_2024,plain,(
    ! [A_652,B_653,B_654,C_655] :
      ( r1_lattices(A_652,k16_lattice3(A_652,B_653),'#skF_2'(A_652,B_654,C_655))
      | ~ m1_subset_1(k16_lattice3(A_652,B_653),u1_struct_0(A_652))
      | ~ r1_tarski(C_655,B_653)
      | r3_lattice3(A_652,B_654,C_655)
      | ~ m1_subset_1(B_654,u1_struct_0(A_652))
      | ~ v4_lattice3(A_652)
      | ~ v10_lattices(A_652)
      | ~ l3_lattices(A_652)
      | v2_struct_0(A_652) ) ),
    inference(resolution,[status(thm)],[c_187,c_1764])).

tff(c_10,plain,(
    ! [A_6,B_18,C_24] :
      ( ~ r1_lattices(A_6,B_18,'#skF_2'(A_6,B_18,C_24))
      | r3_lattice3(A_6,B_18,C_24)
      | ~ m1_subset_1(B_18,u1_struct_0(A_6))
      | ~ l3_lattices(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2033,plain,(
    ! [C_656,B_657,A_658] :
      ( ~ r1_tarski(C_656,B_657)
      | r3_lattice3(A_658,k16_lattice3(A_658,B_657),C_656)
      | ~ m1_subset_1(k16_lattice3(A_658,B_657),u1_struct_0(A_658))
      | ~ v4_lattice3(A_658)
      | ~ v10_lattices(A_658)
      | ~ l3_lattices(A_658)
      | v2_struct_0(A_658) ) ),
    inference(resolution,[status(thm)],[c_2024,c_10])).

tff(c_2049,plain,(
    ! [C_665,B_666,A_667] :
      ( ~ r1_tarski(C_665,B_666)
      | r3_lattice3(A_667,k16_lattice3(A_667,B_666),C_665)
      | ~ v4_lattice3(A_667)
      | ~ v10_lattices(A_667)
      | ~ l3_lattices(A_667)
      | v2_struct_0(A_667) ) ),
    inference(resolution,[status(thm)],[c_26,c_2033])).

tff(c_2149,plain,(
    ! [C_676,A_677,B_678] :
      ( ~ r1_tarski(C_676,a_2_2_lattice3(A_677,B_678))
      | r3_lattice3(A_677,k15_lattice3(A_677,B_678),C_676)
      | ~ v4_lattice3(A_677)
      | ~ v10_lattices(A_677)
      | ~ l3_lattices(A_677)
      | v2_struct_0(A_677)
      | ~ l3_lattices(A_677)
      | ~ v4_lattice3(A_677)
      | ~ v10_lattices(A_677)
      | v2_struct_0(A_677) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2049])).

tff(c_24,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(k15_lattice3(A_50,B_51),u1_struct_0(A_50))
      | ~ l3_lattices(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_214,plain,(
    ! [A_169,B_170,C_171] :
      ( r3_lattices(A_169,B_170,k16_lattice3(A_169,C_171))
      | ~ r3_lattice3(A_169,B_170,C_171)
      | ~ m1_subset_1(B_170,u1_struct_0(A_169))
      | ~ l3_lattices(A_169)
      | ~ v4_lattice3(A_169)
      | ~ v10_lattices(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_452,plain,(
    ! [A_278,B_279,B_280] :
      ( r3_lattices(A_278,B_279,k15_lattice3(A_278,B_280))
      | ~ r3_lattice3(A_278,B_279,a_2_2_lattice3(A_278,B_280))
      | ~ m1_subset_1(B_279,u1_struct_0(A_278))
      | ~ l3_lattices(A_278)
      | ~ v4_lattice3(A_278)
      | ~ v10_lattices(A_278)
      | v2_struct_0(A_278)
      | ~ l3_lattices(A_278)
      | ~ v4_lattice3(A_278)
      | ~ v10_lattices(A_278)
      | v2_struct_0(A_278) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_214])).

tff(c_50,plain,
    ( ~ r3_lattices('#skF_6',k16_lattice3('#skF_6','#skF_8'),k16_lattice3('#skF_6','#skF_7'))
    | ~ r3_lattices('#skF_6',k15_lattice3('#skF_6','#skF_7'),k15_lattice3('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_73,plain,(
    ~ r3_lattices('#skF_6',k15_lattice3('#skF_6','#skF_7'),k15_lattice3('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_459,plain,
    ( ~ r3_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_7'),a_2_2_lattice3('#skF_6','#skF_8'))
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_452,c_73])).

tff(c_463,plain,
    ( ~ r3_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_7'),a_2_2_lattice3('#skF_6','#skF_8'))
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_459])).

tff(c_464,plain,
    ( ~ r3_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_7'),a_2_2_lattice3('#skF_6','#skF_8'))
    | ~ m1_subset_1(k15_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_463])).

tff(c_465,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_464])).

tff(c_468,plain,
    ( ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_465])).

tff(c_471,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_468])).

tff(c_473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_471])).

tff(c_474,plain,(
    ~ r3_lattice3('#skF_6',k15_lattice3('#skF_6','#skF_7'),a_2_2_lattice3('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_464])).

tff(c_2178,plain,
    ( ~ r1_tarski(a_2_2_lattice3('#skF_6','#skF_8'),a_2_2_lattice3('#skF_6','#skF_7'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2149,c_474])).

tff(c_2200,plain,
    ( ~ r1_tarski(a_2_2_lattice3('#skF_6','#skF_8'),a_2_2_lattice3('#skF_6','#skF_7'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2178])).

tff(c_2201,plain,(
    ~ r1_tarski(a_2_2_lattice3('#skF_6','#skF_8'),a_2_2_lattice3('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2200])).

tff(c_4281,plain,
    ( ~ r1_tarski('#skF_7','#skF_7')
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4242,c_2201])).

tff(c_4345,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_67,c_4281])).

tff(c_4347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4345])).

tff(c_4348,plain,(
    ~ r3_lattices('#skF_6',k16_lattice3('#skF_6','#skF_8'),k16_lattice3('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_4502,plain,
    ( ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_7')
    | ~ m1_subset_1(k16_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l3_lattices('#skF_6')
    | ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4499,c_4348])).

tff(c_4508,plain,
    ( ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_7')
    | ~ m1_subset_1(k16_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_4502])).

tff(c_4509,plain,
    ( ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_7')
    | ~ m1_subset_1(k16_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4508])).

tff(c_4510,plain,(
    ~ m1_subset_1(k16_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_4509])).

tff(c_4513,plain,
    ( ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_4510])).

tff(c_4516,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4513])).

tff(c_4518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4516])).

tff(c_4520,plain,(
    m1_subset_1(k16_lattice3('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_4509])).

tff(c_4442,plain,(
    ! [A_1070,B_1071,C_1072] :
      ( r2_hidden('#skF_2'(A_1070,B_1071,C_1072),C_1072)
      | r3_lattice3(A_1070,B_1071,C_1072)
      | ~ m1_subset_1(B_1071,u1_struct_0(A_1070))
      | ~ l3_lattices(A_1070)
      | v2_struct_0(A_1070) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4481,plain,(
    ! [A_1102,B_1103,C_1104,B_1105] :
      ( r2_hidden('#skF_2'(A_1102,B_1103,C_1104),B_1105)
      | ~ r1_tarski(C_1104,B_1105)
      | r3_lattice3(A_1102,B_1103,C_1104)
      | ~ m1_subset_1(B_1103,u1_struct_0(A_1102))
      | ~ l3_lattices(A_1102)
      | v2_struct_0(A_1102) ) ),
    inference(resolution,[status(thm)],[c_4442,c_2])).

tff(c_4586,plain,(
    ! [B_1130,B_1131,C_1132,B_1128,A_1129] :
      ( r2_hidden('#skF_2'(A_1129,B_1130,C_1132),B_1131)
      | ~ r1_tarski(B_1128,B_1131)
      | ~ r1_tarski(C_1132,B_1128)
      | r3_lattice3(A_1129,B_1130,C_1132)
      | ~ m1_subset_1(B_1130,u1_struct_0(A_1129))
      | ~ l3_lattices(A_1129)
      | v2_struct_0(A_1129) ) ),
    inference(resolution,[status(thm)],[c_4481,c_2])).

tff(c_4599,plain,(
    ! [A_1136,B_1137,C_1138] :
      ( r2_hidden('#skF_2'(A_1136,B_1137,C_1138),'#skF_8')
      | ~ r1_tarski(C_1138,'#skF_7')
      | r3_lattice3(A_1136,B_1137,C_1138)
      | ~ m1_subset_1(B_1137,u1_struct_0(A_1136))
      | ~ l3_lattices(A_1136)
      | v2_struct_0(A_1136) ) ),
    inference(resolution,[status(thm)],[c_52,c_4586])).

tff(c_8,plain,(
    ! [A_6,B_18,D_27,C_24] :
      ( r1_lattices(A_6,B_18,D_27)
      | ~ r2_hidden(D_27,C_24)
      | ~ m1_subset_1(D_27,u1_struct_0(A_6))
      | ~ r3_lattice3(A_6,B_18,C_24)
      | ~ m1_subset_1(B_18,u1_struct_0(A_6))
      | ~ l3_lattices(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4746,plain,(
    ! [A_1217,A_1218,B_1216,C_1219,B_1215] :
      ( r1_lattices(A_1217,B_1216,'#skF_2'(A_1218,B_1215,C_1219))
      | ~ m1_subset_1('#skF_2'(A_1218,B_1215,C_1219),u1_struct_0(A_1217))
      | ~ r3_lattice3(A_1217,B_1216,'#skF_8')
      | ~ m1_subset_1(B_1216,u1_struct_0(A_1217))
      | ~ l3_lattices(A_1217)
      | v2_struct_0(A_1217)
      | ~ r1_tarski(C_1219,'#skF_7')
      | r3_lattice3(A_1218,B_1215,C_1219)
      | ~ m1_subset_1(B_1215,u1_struct_0(A_1218))
      | ~ l3_lattices(A_1218)
      | v2_struct_0(A_1218) ) ),
    inference(resolution,[status(thm)],[c_4599,c_8])).

tff(c_4868,plain,(
    ! [A_1235,B_1236,B_1237,C_1238] :
      ( r1_lattices(A_1235,B_1236,'#skF_2'(A_1235,B_1237,C_1238))
      | ~ r3_lattice3(A_1235,B_1236,'#skF_8')
      | ~ m1_subset_1(B_1236,u1_struct_0(A_1235))
      | ~ r1_tarski(C_1238,'#skF_7')
      | r3_lattice3(A_1235,B_1237,C_1238)
      | ~ m1_subset_1(B_1237,u1_struct_0(A_1235))
      | ~ l3_lattices(A_1235)
      | v2_struct_0(A_1235) ) ),
    inference(resolution,[status(thm)],[c_14,c_4746])).

tff(c_4879,plain,(
    ! [A_1239,B_1240,C_1241] :
      ( ~ r3_lattice3(A_1239,B_1240,'#skF_8')
      | ~ r1_tarski(C_1241,'#skF_7')
      | r3_lattice3(A_1239,B_1240,C_1241)
      | ~ m1_subset_1(B_1240,u1_struct_0(A_1239))
      | ~ l3_lattices(A_1239)
      | v2_struct_0(A_1239) ) ),
    inference(resolution,[status(thm)],[c_4868,c_10])).

tff(c_4883,plain,(
    ! [C_1241] :
      ( ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_8')
      | ~ r1_tarski(C_1241,'#skF_7')
      | r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_1241)
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4520,c_4879])).

tff(c_4897,plain,(
    ! [C_1241] :
      ( ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_8')
      | ~ r1_tarski(C_1241,'#skF_7')
      | r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_1241)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4883])).

tff(c_4898,plain,(
    ! [C_1241] :
      ( ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_8')
      | ~ r1_tarski(C_1241,'#skF_7')
      | r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_1241) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4897])).

tff(c_4904,plain,(
    ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4898])).

tff(c_4907,plain,
    ( ~ v4_lattice3('#skF_6')
    | ~ v10_lattices('#skF_6')
    | ~ l3_lattices('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4463,c_4904])).

tff(c_4910,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_56,c_4907])).

tff(c_4912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4910])).

tff(c_4915,plain,(
    ! [C_1242] :
      ( ~ r1_tarski(C_1242,'#skF_7')
      | r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),C_1242) ) ),
    inference(splitRight,[status(thm)],[c_4898])).

tff(c_4519,plain,(
    ~ r3_lattice3('#skF_6',k16_lattice3('#skF_6','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_4509])).

tff(c_4918,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_4915,c_4519])).

tff(c_4922,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_4918])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:40:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.84/2.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.84/2.95  
% 8.84/2.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.84/2.95  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > r1_tarski > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1
% 8.84/2.95  
% 8.84/2.95  %Foreground sorts:
% 8.84/2.95  
% 8.84/2.95  
% 8.84/2.95  %Background operators:
% 8.84/2.95  
% 8.84/2.95  
% 8.84/2.95  %Foreground operators:
% 8.84/2.95  tff(l3_lattices, type, l3_lattices: $i > $o).
% 8.84/2.95  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.84/2.95  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 8.84/2.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.84/2.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.84/2.95  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 8.84/2.95  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 8.84/2.95  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.84/2.95  tff('#skF_7', type, '#skF_7': $i).
% 8.84/2.95  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 8.84/2.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.84/2.95  tff('#skF_6', type, '#skF_6': $i).
% 8.84/2.95  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 8.84/2.95  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 8.84/2.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.84/2.95  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 8.84/2.95  tff(v10_lattices, type, v10_lattices: $i > $o).
% 8.84/2.95  tff(a_2_2_lattice3, type, a_2_2_lattice3: ($i * $i) > $i).
% 8.84/2.95  tff('#skF_8', type, '#skF_8': $i).
% 8.84/2.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.84/2.95  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.84/2.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.84/2.95  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.84/2.95  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.84/2.95  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 8.84/2.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.84/2.95  
% 8.84/2.98  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.84/2.98  tff(f_170, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (r1_tarski(B, C) => (r3_lattices(A, k15_lattice3(A, B), k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), k16_lattice3(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_lattice3)).
% 8.84/2.98  tff(f_82, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k16_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 8.84/2.98  tff(f_124, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_lattice3)).
% 8.84/2.98  tff(f_153, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) => r3_lattices(A, B, k16_lattice3(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_lattice3)).
% 8.84/2.98  tff(f_100, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_2_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r4_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 8.84/2.98  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 8.84/2.98  tff(f_136, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (k15_lattice3(A, B) = k16_lattice3(A, a_2_2_lattice3(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 8.84/2.98  tff(f_50, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 8.84/2.98  tff(f_75, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 8.84/2.98  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.84/2.98  tff(c_62, plain, (![A_96, B_97]: (~r2_hidden('#skF_1'(A_96, B_97), B_97) | r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.84/2.98  tff(c_67, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_62])).
% 8.84/2.98  tff(c_60, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_170])).
% 8.84/2.98  tff(c_54, plain, (l3_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_170])).
% 8.84/2.98  tff(c_58, plain, (v10_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_170])).
% 8.84/2.98  tff(c_56, plain, (v4_lattice3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_170])).
% 8.84/2.98  tff(c_26, plain, (![A_52, B_53]: (m1_subset_1(k16_lattice3(A_52, B_53), u1_struct_0(A_52)) | ~l3_lattices(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.84/2.98  tff(c_4458, plain, (![A_1095, C_1096]: (r3_lattice3(A_1095, k16_lattice3(A_1095, C_1096), C_1096) | ~m1_subset_1(k16_lattice3(A_1095, C_1096), u1_struct_0(A_1095)) | ~l3_lattices(A_1095) | ~v4_lattice3(A_1095) | ~v10_lattices(A_1095) | v2_struct_0(A_1095))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.84/2.98  tff(c_4463, plain, (![A_52, B_53]: (r3_lattice3(A_52, k16_lattice3(A_52, B_53), B_53) | ~v4_lattice3(A_52) | ~v10_lattices(A_52) | ~l3_lattices(A_52) | v2_struct_0(A_52))), inference(resolution, [status(thm)], [c_26, c_4458])).
% 8.84/2.98  tff(c_4499, plain, (![A_1110, B_1111, C_1112]: (r3_lattices(A_1110, B_1111, k16_lattice3(A_1110, C_1112)) | ~r3_lattice3(A_1110, B_1111, C_1112) | ~m1_subset_1(B_1111, u1_struct_0(A_1110)) | ~l3_lattices(A_1110) | ~v4_lattice3(A_1110) | ~v10_lattices(A_1110) | v2_struct_0(A_1110))), inference(cnfTransformation, [status(thm)], [f_153])).
% 8.84/2.98  tff(c_69, plain, (![C_99, B_100, A_101]: (r2_hidden(C_99, B_100) | ~r2_hidden(C_99, A_101) | ~r1_tarski(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.84/2.98  tff(c_72, plain, (![A_1, B_2, B_100]: (r2_hidden('#skF_1'(A_1, B_2), B_100) | ~r1_tarski(A_1, B_100) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_69])).
% 8.84/2.98  tff(c_141, plain, (![A_127, B_128, C_129]: ('#skF_4'(A_127, B_128, C_129)=A_127 | ~r2_hidden(A_127, a_2_2_lattice3(B_128, C_129)) | ~l3_lattices(B_128) | ~v4_lattice3(B_128) | ~v10_lattices(B_128) | v2_struct_0(B_128))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.84/2.98  tff(c_364, plain, (![B_228, C_229, B_230]: ('#skF_4'('#skF_1'(a_2_2_lattice3(B_228, C_229), B_230), B_228, C_229)='#skF_1'(a_2_2_lattice3(B_228, C_229), B_230) | ~l3_lattices(B_228) | ~v4_lattice3(B_228) | ~v10_lattices(B_228) | v2_struct_0(B_228) | r1_tarski(a_2_2_lattice3(B_228, C_229), B_230))), inference(resolution, [status(thm)], [c_6, c_141])).
% 8.84/2.98  tff(c_34, plain, (![A_54, B_55, C_56]: (m1_subset_1('#skF_4'(A_54, B_55, C_56), u1_struct_0(B_55)) | ~r2_hidden(A_54, a_2_2_lattice3(B_55, C_56)) | ~l3_lattices(B_55) | ~v4_lattice3(B_55) | ~v10_lattices(B_55) | v2_struct_0(B_55))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.84/2.98  tff(c_1178, plain, (![B_459, C_460, B_461]: (m1_subset_1('#skF_1'(a_2_2_lattice3(B_459, C_460), B_461), u1_struct_0(B_459)) | ~r2_hidden('#skF_1'(a_2_2_lattice3(B_459, C_460), B_461), a_2_2_lattice3(B_459, C_460)) | ~l3_lattices(B_459) | ~v4_lattice3(B_459) | ~v10_lattices(B_459) | v2_struct_0(B_459) | ~l3_lattices(B_459) | ~v4_lattice3(B_459) | ~v10_lattices(B_459) | v2_struct_0(B_459) | r1_tarski(a_2_2_lattice3(B_459, C_460), B_461))), inference(superposition, [status(thm), theory('equality')], [c_364, c_34])).
% 8.84/2.98  tff(c_1190, plain, (![B_459, C_460, B_2]: (m1_subset_1('#skF_1'(a_2_2_lattice3(B_459, C_460), B_2), u1_struct_0(B_459)) | ~l3_lattices(B_459) | ~v4_lattice3(B_459) | ~v10_lattices(B_459) | v2_struct_0(B_459) | ~r1_tarski(a_2_2_lattice3(B_459, C_460), a_2_2_lattice3(B_459, C_460)) | r1_tarski(a_2_2_lattice3(B_459, C_460), B_2))), inference(resolution, [status(thm)], [c_72, c_1178])).
% 8.84/2.98  tff(c_1199, plain, (![B_459, C_460, B_2]: (m1_subset_1('#skF_1'(a_2_2_lattice3(B_459, C_460), B_2), u1_struct_0(B_459)) | ~l3_lattices(B_459) | ~v4_lattice3(B_459) | ~v10_lattices(B_459) | v2_struct_0(B_459) | r1_tarski(a_2_2_lattice3(B_459, C_460), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_1190])).
% 8.84/2.98  tff(c_30, plain, (![B_55, A_54, C_56]: (r4_lattice3(B_55, '#skF_4'(A_54, B_55, C_56), C_56) | ~r2_hidden(A_54, a_2_2_lattice3(B_55, C_56)) | ~l3_lattices(B_55) | ~v4_lattice3(B_55) | ~v10_lattices(B_55) | v2_struct_0(B_55))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.84/2.98  tff(c_1127, plain, (![B_450, C_451, B_452]: (r4_lattice3(B_450, '#skF_1'(a_2_2_lattice3(B_450, C_451), B_452), C_451) | ~r2_hidden('#skF_1'(a_2_2_lattice3(B_450, C_451), B_452), a_2_2_lattice3(B_450, C_451)) | ~l3_lattices(B_450) | ~v4_lattice3(B_450) | ~v10_lattices(B_450) | v2_struct_0(B_450) | ~l3_lattices(B_450) | ~v4_lattice3(B_450) | ~v10_lattices(B_450) | v2_struct_0(B_450) | r1_tarski(a_2_2_lattice3(B_450, C_451), B_452))), inference(superposition, [status(thm), theory('equality')], [c_364, c_30])).
% 8.84/2.98  tff(c_1139, plain, (![B_450, C_451, B_2]: (r4_lattice3(B_450, '#skF_1'(a_2_2_lattice3(B_450, C_451), B_2), C_451) | ~l3_lattices(B_450) | ~v4_lattice3(B_450) | ~v10_lattices(B_450) | v2_struct_0(B_450) | ~r1_tarski(a_2_2_lattice3(B_450, C_451), a_2_2_lattice3(B_450, C_451)) | r1_tarski(a_2_2_lattice3(B_450, C_451), B_2))), inference(resolution, [status(thm)], [c_72, c_1127])).
% 8.84/2.98  tff(c_1148, plain, (![B_450, C_451, B_2]: (r4_lattice3(B_450, '#skF_1'(a_2_2_lattice3(B_450, C_451), B_2), C_451) | ~l3_lattices(B_450) | ~v4_lattice3(B_450) | ~v10_lattices(B_450) | v2_struct_0(B_450) | r1_tarski(a_2_2_lattice3(B_450, C_451), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_1139])).
% 8.84/2.98  tff(c_22, plain, (![A_28, B_40, C_46]: (m1_subset_1('#skF_3'(A_28, B_40, C_46), u1_struct_0(A_28)) | r4_lattice3(A_28, B_40, C_46) | ~m1_subset_1(B_40, u1_struct_0(A_28)) | ~l3_lattices(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.84/2.98  tff(c_52, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_170])).
% 8.84/2.98  tff(c_157, plain, (![A_130, B_131, C_132]: (r2_hidden('#skF_3'(A_130, B_131, C_132), C_132) | r4_lattice3(A_130, B_131, C_132) | ~m1_subset_1(B_131, u1_struct_0(A_130)) | ~l3_lattices(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.84/2.98  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.84/2.98  tff(c_218, plain, (![A_172, B_173, C_174, B_175]: (r2_hidden('#skF_3'(A_172, B_173, C_174), B_175) | ~r1_tarski(C_174, B_175) | r4_lattice3(A_172, B_173, C_174) | ~m1_subset_1(B_173, u1_struct_0(A_172)) | ~l3_lattices(A_172) | v2_struct_0(A_172))), inference(resolution, [status(thm)], [c_157, c_2])).
% 8.84/2.98  tff(c_312, plain, (![B_208, B_212, C_211, B_209, A_210]: (r2_hidden('#skF_3'(A_210, B_208, C_211), B_209) | ~r1_tarski(B_212, B_209) | ~r1_tarski(C_211, B_212) | r4_lattice3(A_210, B_208, C_211) | ~m1_subset_1(B_208, u1_struct_0(A_210)) | ~l3_lattices(A_210) | v2_struct_0(A_210))), inference(resolution, [status(thm)], [c_218, c_2])).
% 8.84/2.98  tff(c_319, plain, (![A_213, B_214, C_215]: (r2_hidden('#skF_3'(A_213, B_214, C_215), '#skF_8') | ~r1_tarski(C_215, '#skF_7') | r4_lattice3(A_213, B_214, C_215) | ~m1_subset_1(B_214, u1_struct_0(A_213)) | ~l3_lattices(A_213) | v2_struct_0(A_213))), inference(resolution, [status(thm)], [c_52, c_312])).
% 8.84/2.98  tff(c_16, plain, (![A_28, D_49, B_40, C_46]: (r1_lattices(A_28, D_49, B_40) | ~r2_hidden(D_49, C_46) | ~m1_subset_1(D_49, u1_struct_0(A_28)) | ~r4_lattice3(A_28, B_40, C_46) | ~m1_subset_1(B_40, u1_struct_0(A_28)) | ~l3_lattices(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.84/2.98  tff(c_3380, plain, (![B_964, A_961, C_965, A_963, B_962]: (r1_lattices(A_963, '#skF_3'(A_961, B_964, C_965), B_962) | ~m1_subset_1('#skF_3'(A_961, B_964, C_965), u1_struct_0(A_963)) | ~r4_lattice3(A_963, B_962, '#skF_8') | ~m1_subset_1(B_962, u1_struct_0(A_963)) | ~l3_lattices(A_963) | v2_struct_0(A_963) | ~r1_tarski(C_965, '#skF_7') | r4_lattice3(A_961, B_964, C_965) | ~m1_subset_1(B_964, u1_struct_0(A_961)) | ~l3_lattices(A_961) | v2_struct_0(A_961))), inference(resolution, [status(thm)], [c_319, c_16])).
% 8.84/2.98  tff(c_3387, plain, (![A_966, B_967, C_968, B_969]: (r1_lattices(A_966, '#skF_3'(A_966, B_967, C_968), B_969) | ~r4_lattice3(A_966, B_969, '#skF_8') | ~m1_subset_1(B_969, u1_struct_0(A_966)) | ~r1_tarski(C_968, '#skF_7') | r4_lattice3(A_966, B_967, C_968) | ~m1_subset_1(B_967, u1_struct_0(A_966)) | ~l3_lattices(A_966) | v2_struct_0(A_966))), inference(resolution, [status(thm)], [c_22, c_3380])).
% 8.84/2.98  tff(c_18, plain, (![A_28, B_40, C_46]: (~r1_lattices(A_28, '#skF_3'(A_28, B_40, C_46), B_40) | r4_lattice3(A_28, B_40, C_46) | ~m1_subset_1(B_40, u1_struct_0(A_28)) | ~l3_lattices(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.84/2.98  tff(c_3398, plain, (![A_970, B_971, C_972]: (~r4_lattice3(A_970, B_971, '#skF_8') | ~r1_tarski(C_972, '#skF_7') | r4_lattice3(A_970, B_971, C_972) | ~m1_subset_1(B_971, u1_struct_0(A_970)) | ~l3_lattices(A_970) | v2_struct_0(A_970))), inference(resolution, [status(thm)], [c_3387, c_18])).
% 8.84/2.98  tff(c_4094, plain, (![B_1022, C_1023, B_1024, C_1025]: (~r4_lattice3(B_1022, '#skF_1'(a_2_2_lattice3(B_1022, C_1023), B_1024), '#skF_8') | ~r1_tarski(C_1025, '#skF_7') | r4_lattice3(B_1022, '#skF_1'(a_2_2_lattice3(B_1022, C_1023), B_1024), C_1025) | ~l3_lattices(B_1022) | ~v4_lattice3(B_1022) | ~v10_lattices(B_1022) | v2_struct_0(B_1022) | r1_tarski(a_2_2_lattice3(B_1022, C_1023), B_1024))), inference(resolution, [status(thm)], [c_1199, c_3398])).
% 8.84/2.98  tff(c_4099, plain, (![C_1026, B_1027, B_1028]: (~r1_tarski(C_1026, '#skF_7') | r4_lattice3(B_1027, '#skF_1'(a_2_2_lattice3(B_1027, '#skF_8'), B_1028), C_1026) | ~l3_lattices(B_1027) | ~v4_lattice3(B_1027) | ~v10_lattices(B_1027) | v2_struct_0(B_1027) | r1_tarski(a_2_2_lattice3(B_1027, '#skF_8'), B_1028))), inference(resolution, [status(thm)], [c_1148, c_4094])).
% 8.84/2.98  tff(c_192, plain, (![D_162, B_163, C_164]: (r2_hidden(D_162, a_2_2_lattice3(B_163, C_164)) | ~r4_lattice3(B_163, D_162, C_164) | ~m1_subset_1(D_162, u1_struct_0(B_163)) | ~l3_lattices(B_163) | ~v4_lattice3(B_163) | ~v10_lattices(B_163) | v2_struct_0(B_163))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.84/2.98  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.84/2.98  tff(c_204, plain, (![A_1, B_163, C_164]: (r1_tarski(A_1, a_2_2_lattice3(B_163, C_164)) | ~r4_lattice3(B_163, '#skF_1'(A_1, a_2_2_lattice3(B_163, C_164)), C_164) | ~m1_subset_1('#skF_1'(A_1, a_2_2_lattice3(B_163, C_164)), u1_struct_0(B_163)) | ~l3_lattices(B_163) | ~v4_lattice3(B_163) | ~v10_lattices(B_163) | v2_struct_0(B_163))), inference(resolution, [status(thm)], [c_192, c_4])).
% 8.84/2.98  tff(c_4236, plain, (![B_1035, C_1036]: (~m1_subset_1('#skF_1'(a_2_2_lattice3(B_1035, '#skF_8'), a_2_2_lattice3(B_1035, C_1036)), u1_struct_0(B_1035)) | ~r1_tarski(C_1036, '#skF_7') | ~l3_lattices(B_1035) | ~v4_lattice3(B_1035) | ~v10_lattices(B_1035) | v2_struct_0(B_1035) | r1_tarski(a_2_2_lattice3(B_1035, '#skF_8'), a_2_2_lattice3(B_1035, C_1036)))), inference(resolution, [status(thm)], [c_4099, c_204])).
% 8.84/2.98  tff(c_4242, plain, (![C_1037, B_1038]: (~r1_tarski(C_1037, '#skF_7') | ~l3_lattices(B_1038) | ~v4_lattice3(B_1038) | ~v10_lattices(B_1038) | v2_struct_0(B_1038) | r1_tarski(a_2_2_lattice3(B_1038, '#skF_8'), a_2_2_lattice3(B_1038, C_1037)))), inference(resolution, [status(thm)], [c_1199, c_4236])).
% 8.84/2.98  tff(c_46, plain, (![A_82, B_84]: (k16_lattice3(A_82, a_2_2_lattice3(A_82, B_84))=k15_lattice3(A_82, B_84) | ~l3_lattices(A_82) | ~v4_lattice3(A_82) | ~v10_lattices(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.84/2.98  tff(c_182, plain, (![A_158, C_159]: (r3_lattice3(A_158, k16_lattice3(A_158, C_159), C_159) | ~m1_subset_1(k16_lattice3(A_158, C_159), u1_struct_0(A_158)) | ~l3_lattices(A_158) | ~v4_lattice3(A_158) | ~v10_lattices(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.84/2.98  tff(c_187, plain, (![A_52, B_53]: (r3_lattice3(A_52, k16_lattice3(A_52, B_53), B_53) | ~v4_lattice3(A_52) | ~v10_lattices(A_52) | ~l3_lattices(A_52) | v2_struct_0(A_52))), inference(resolution, [status(thm)], [c_26, c_182])).
% 8.84/2.98  tff(c_14, plain, (![A_6, B_18, C_24]: (m1_subset_1('#skF_2'(A_6, B_18, C_24), u1_struct_0(A_6)) | r3_lattice3(A_6, B_18, C_24) | ~m1_subset_1(B_18, u1_struct_0(A_6)) | ~l3_lattices(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.84/2.98  tff(c_166, plain, (![A_133, B_134, C_135]: (r2_hidden('#skF_2'(A_133, B_134, C_135), C_135) | r3_lattice3(A_133, B_134, C_135) | ~m1_subset_1(B_134, u1_struct_0(A_133)) | ~l3_lattices(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.84/2.98  tff(c_174, plain, (![A_133, B_134, C_135, B_2]: (r2_hidden('#skF_2'(A_133, B_134, C_135), B_2) | ~r1_tarski(C_135, B_2) | r3_lattice3(A_133, B_134, C_135) | ~m1_subset_1(B_134, u1_struct_0(A_133)) | ~l3_lattices(A_133) | v2_struct_0(A_133))), inference(resolution, [status(thm)], [c_166, c_2])).
% 8.84/2.98  tff(c_231, plain, (![A_179, B_180, D_181, C_182]: (r1_lattices(A_179, B_180, D_181) | ~r2_hidden(D_181, C_182) | ~m1_subset_1(D_181, u1_struct_0(A_179)) | ~r3_lattice3(A_179, B_180, C_182) | ~m1_subset_1(B_180, u1_struct_0(A_179)) | ~l3_lattices(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.84/2.98  tff(c_1706, plain, (![C_580, B_584, A_579, B_581, B_582, A_583]: (r1_lattices(A_583, B_581, '#skF_2'(A_579, B_582, C_580)) | ~m1_subset_1('#skF_2'(A_579, B_582, C_580), u1_struct_0(A_583)) | ~r3_lattice3(A_583, B_581, B_584) | ~m1_subset_1(B_581, u1_struct_0(A_583)) | ~l3_lattices(A_583) | v2_struct_0(A_583) | ~r1_tarski(C_580, B_584) | r3_lattice3(A_579, B_582, C_580) | ~m1_subset_1(B_582, u1_struct_0(A_579)) | ~l3_lattices(A_579) | v2_struct_0(A_579))), inference(resolution, [status(thm)], [c_174, c_231])).
% 8.84/2.98  tff(c_1764, plain, (![B_590, B_591, B_592, C_589, A_593]: (r1_lattices(A_593, B_592, '#skF_2'(A_593, B_591, C_589)) | ~r3_lattice3(A_593, B_592, B_590) | ~m1_subset_1(B_592, u1_struct_0(A_593)) | ~r1_tarski(C_589, B_590) | r3_lattice3(A_593, B_591, C_589) | ~m1_subset_1(B_591, u1_struct_0(A_593)) | ~l3_lattices(A_593) | v2_struct_0(A_593))), inference(resolution, [status(thm)], [c_14, c_1706])).
% 8.84/2.98  tff(c_2024, plain, (![A_652, B_653, B_654, C_655]: (r1_lattices(A_652, k16_lattice3(A_652, B_653), '#skF_2'(A_652, B_654, C_655)) | ~m1_subset_1(k16_lattice3(A_652, B_653), u1_struct_0(A_652)) | ~r1_tarski(C_655, B_653) | r3_lattice3(A_652, B_654, C_655) | ~m1_subset_1(B_654, u1_struct_0(A_652)) | ~v4_lattice3(A_652) | ~v10_lattices(A_652) | ~l3_lattices(A_652) | v2_struct_0(A_652))), inference(resolution, [status(thm)], [c_187, c_1764])).
% 8.84/2.98  tff(c_10, plain, (![A_6, B_18, C_24]: (~r1_lattices(A_6, B_18, '#skF_2'(A_6, B_18, C_24)) | r3_lattice3(A_6, B_18, C_24) | ~m1_subset_1(B_18, u1_struct_0(A_6)) | ~l3_lattices(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.84/2.98  tff(c_2033, plain, (![C_656, B_657, A_658]: (~r1_tarski(C_656, B_657) | r3_lattice3(A_658, k16_lattice3(A_658, B_657), C_656) | ~m1_subset_1(k16_lattice3(A_658, B_657), u1_struct_0(A_658)) | ~v4_lattice3(A_658) | ~v10_lattices(A_658) | ~l3_lattices(A_658) | v2_struct_0(A_658))), inference(resolution, [status(thm)], [c_2024, c_10])).
% 8.84/2.98  tff(c_2049, plain, (![C_665, B_666, A_667]: (~r1_tarski(C_665, B_666) | r3_lattice3(A_667, k16_lattice3(A_667, B_666), C_665) | ~v4_lattice3(A_667) | ~v10_lattices(A_667) | ~l3_lattices(A_667) | v2_struct_0(A_667))), inference(resolution, [status(thm)], [c_26, c_2033])).
% 8.84/2.98  tff(c_2149, plain, (![C_676, A_677, B_678]: (~r1_tarski(C_676, a_2_2_lattice3(A_677, B_678)) | r3_lattice3(A_677, k15_lattice3(A_677, B_678), C_676) | ~v4_lattice3(A_677) | ~v10_lattices(A_677) | ~l3_lattices(A_677) | v2_struct_0(A_677) | ~l3_lattices(A_677) | ~v4_lattice3(A_677) | ~v10_lattices(A_677) | v2_struct_0(A_677))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2049])).
% 8.84/2.98  tff(c_24, plain, (![A_50, B_51]: (m1_subset_1(k15_lattice3(A_50, B_51), u1_struct_0(A_50)) | ~l3_lattices(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.84/2.98  tff(c_214, plain, (![A_169, B_170, C_171]: (r3_lattices(A_169, B_170, k16_lattice3(A_169, C_171)) | ~r3_lattice3(A_169, B_170, C_171) | ~m1_subset_1(B_170, u1_struct_0(A_169)) | ~l3_lattices(A_169) | ~v4_lattice3(A_169) | ~v10_lattices(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_153])).
% 8.84/2.98  tff(c_452, plain, (![A_278, B_279, B_280]: (r3_lattices(A_278, B_279, k15_lattice3(A_278, B_280)) | ~r3_lattice3(A_278, B_279, a_2_2_lattice3(A_278, B_280)) | ~m1_subset_1(B_279, u1_struct_0(A_278)) | ~l3_lattices(A_278) | ~v4_lattice3(A_278) | ~v10_lattices(A_278) | v2_struct_0(A_278) | ~l3_lattices(A_278) | ~v4_lattice3(A_278) | ~v10_lattices(A_278) | v2_struct_0(A_278))), inference(superposition, [status(thm), theory('equality')], [c_46, c_214])).
% 8.84/2.98  tff(c_50, plain, (~r3_lattices('#skF_6', k16_lattice3('#skF_6', '#skF_8'), k16_lattice3('#skF_6', '#skF_7')) | ~r3_lattices('#skF_6', k15_lattice3('#skF_6', '#skF_7'), k15_lattice3('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 8.84/2.98  tff(c_73, plain, (~r3_lattices('#skF_6', k15_lattice3('#skF_6', '#skF_7'), k15_lattice3('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_50])).
% 8.84/2.98  tff(c_459, plain, (~r3_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_7'), a_2_2_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_452, c_73])).
% 8.84/2.98  tff(c_463, plain, (~r3_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_7'), a_2_2_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_459])).
% 8.84/2.98  tff(c_464, plain, (~r3_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_7'), a_2_2_lattice3('#skF_6', '#skF_8')) | ~m1_subset_1(k15_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_463])).
% 8.84/2.98  tff(c_465, plain, (~m1_subset_1(k15_lattice3('#skF_6', '#skF_7'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_464])).
% 8.84/2.98  tff(c_468, plain, (~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_24, c_465])).
% 8.84/2.98  tff(c_471, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_468])).
% 8.84/2.98  tff(c_473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_471])).
% 8.84/2.98  tff(c_474, plain, (~r3_lattice3('#skF_6', k15_lattice3('#skF_6', '#skF_7'), a_2_2_lattice3('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_464])).
% 8.84/2.98  tff(c_2178, plain, (~r1_tarski(a_2_2_lattice3('#skF_6', '#skF_8'), a_2_2_lattice3('#skF_6', '#skF_7')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_2149, c_474])).
% 8.84/2.98  tff(c_2200, plain, (~r1_tarski(a_2_2_lattice3('#skF_6', '#skF_8'), a_2_2_lattice3('#skF_6', '#skF_7')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2178])).
% 8.84/2.98  tff(c_2201, plain, (~r1_tarski(a_2_2_lattice3('#skF_6', '#skF_8'), a_2_2_lattice3('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_60, c_2200])).
% 8.84/2.98  tff(c_4281, plain, (~r1_tarski('#skF_7', '#skF_7') | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_4242, c_2201])).
% 8.84/2.98  tff(c_4345, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_67, c_4281])).
% 8.84/2.98  tff(c_4347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_4345])).
% 8.84/2.98  tff(c_4348, plain, (~r3_lattices('#skF_6', k16_lattice3('#skF_6', '#skF_8'), k16_lattice3('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_50])).
% 8.84/2.98  tff(c_4502, plain, (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_7') | ~m1_subset_1(k16_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_4499, c_4348])).
% 8.84/2.98  tff(c_4508, plain, (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_7') | ~m1_subset_1(k16_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_4502])).
% 8.84/2.98  tff(c_4509, plain, (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_7') | ~m1_subset_1(k16_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_4508])).
% 8.84/2.98  tff(c_4510, plain, (~m1_subset_1(k16_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_4509])).
% 8.84/2.98  tff(c_4513, plain, (~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_26, c_4510])).
% 8.84/2.98  tff(c_4516, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4513])).
% 8.84/2.98  tff(c_4518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_4516])).
% 8.84/2.98  tff(c_4520, plain, (m1_subset_1(k16_lattice3('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_4509])).
% 8.84/2.98  tff(c_4442, plain, (![A_1070, B_1071, C_1072]: (r2_hidden('#skF_2'(A_1070, B_1071, C_1072), C_1072) | r3_lattice3(A_1070, B_1071, C_1072) | ~m1_subset_1(B_1071, u1_struct_0(A_1070)) | ~l3_lattices(A_1070) | v2_struct_0(A_1070))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.84/2.98  tff(c_4481, plain, (![A_1102, B_1103, C_1104, B_1105]: (r2_hidden('#skF_2'(A_1102, B_1103, C_1104), B_1105) | ~r1_tarski(C_1104, B_1105) | r3_lattice3(A_1102, B_1103, C_1104) | ~m1_subset_1(B_1103, u1_struct_0(A_1102)) | ~l3_lattices(A_1102) | v2_struct_0(A_1102))), inference(resolution, [status(thm)], [c_4442, c_2])).
% 8.84/2.98  tff(c_4586, plain, (![B_1130, B_1131, C_1132, B_1128, A_1129]: (r2_hidden('#skF_2'(A_1129, B_1130, C_1132), B_1131) | ~r1_tarski(B_1128, B_1131) | ~r1_tarski(C_1132, B_1128) | r3_lattice3(A_1129, B_1130, C_1132) | ~m1_subset_1(B_1130, u1_struct_0(A_1129)) | ~l3_lattices(A_1129) | v2_struct_0(A_1129))), inference(resolution, [status(thm)], [c_4481, c_2])).
% 8.84/2.98  tff(c_4599, plain, (![A_1136, B_1137, C_1138]: (r2_hidden('#skF_2'(A_1136, B_1137, C_1138), '#skF_8') | ~r1_tarski(C_1138, '#skF_7') | r3_lattice3(A_1136, B_1137, C_1138) | ~m1_subset_1(B_1137, u1_struct_0(A_1136)) | ~l3_lattices(A_1136) | v2_struct_0(A_1136))), inference(resolution, [status(thm)], [c_52, c_4586])).
% 8.84/2.98  tff(c_8, plain, (![A_6, B_18, D_27, C_24]: (r1_lattices(A_6, B_18, D_27) | ~r2_hidden(D_27, C_24) | ~m1_subset_1(D_27, u1_struct_0(A_6)) | ~r3_lattice3(A_6, B_18, C_24) | ~m1_subset_1(B_18, u1_struct_0(A_6)) | ~l3_lattices(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.84/2.98  tff(c_4746, plain, (![A_1217, A_1218, B_1216, C_1219, B_1215]: (r1_lattices(A_1217, B_1216, '#skF_2'(A_1218, B_1215, C_1219)) | ~m1_subset_1('#skF_2'(A_1218, B_1215, C_1219), u1_struct_0(A_1217)) | ~r3_lattice3(A_1217, B_1216, '#skF_8') | ~m1_subset_1(B_1216, u1_struct_0(A_1217)) | ~l3_lattices(A_1217) | v2_struct_0(A_1217) | ~r1_tarski(C_1219, '#skF_7') | r3_lattice3(A_1218, B_1215, C_1219) | ~m1_subset_1(B_1215, u1_struct_0(A_1218)) | ~l3_lattices(A_1218) | v2_struct_0(A_1218))), inference(resolution, [status(thm)], [c_4599, c_8])).
% 8.84/2.98  tff(c_4868, plain, (![A_1235, B_1236, B_1237, C_1238]: (r1_lattices(A_1235, B_1236, '#skF_2'(A_1235, B_1237, C_1238)) | ~r3_lattice3(A_1235, B_1236, '#skF_8') | ~m1_subset_1(B_1236, u1_struct_0(A_1235)) | ~r1_tarski(C_1238, '#skF_7') | r3_lattice3(A_1235, B_1237, C_1238) | ~m1_subset_1(B_1237, u1_struct_0(A_1235)) | ~l3_lattices(A_1235) | v2_struct_0(A_1235))), inference(resolution, [status(thm)], [c_14, c_4746])).
% 8.84/2.98  tff(c_4879, plain, (![A_1239, B_1240, C_1241]: (~r3_lattice3(A_1239, B_1240, '#skF_8') | ~r1_tarski(C_1241, '#skF_7') | r3_lattice3(A_1239, B_1240, C_1241) | ~m1_subset_1(B_1240, u1_struct_0(A_1239)) | ~l3_lattices(A_1239) | v2_struct_0(A_1239))), inference(resolution, [status(thm)], [c_4868, c_10])).
% 8.84/2.98  tff(c_4883, plain, (![C_1241]: (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_8') | ~r1_tarski(C_1241, '#skF_7') | r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_1241) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_4520, c_4879])).
% 8.84/2.98  tff(c_4897, plain, (![C_1241]: (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_8') | ~r1_tarski(C_1241, '#skF_7') | r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_1241) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4883])).
% 8.84/2.98  tff(c_4898, plain, (![C_1241]: (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_8') | ~r1_tarski(C_1241, '#skF_7') | r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_1241))), inference(negUnitSimplification, [status(thm)], [c_60, c_4897])).
% 8.84/2.98  tff(c_4904, plain, (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_8')), inference(splitLeft, [status(thm)], [c_4898])).
% 8.84/2.98  tff(c_4907, plain, (~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_4463, c_4904])).
% 8.84/2.98  tff(c_4910, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_56, c_4907])).
% 8.84/2.98  tff(c_4912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_4910])).
% 8.84/2.98  tff(c_4915, plain, (![C_1242]: (~r1_tarski(C_1242, '#skF_7') | r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), C_1242))), inference(splitRight, [status(thm)], [c_4898])).
% 8.84/2.98  tff(c_4519, plain, (~r3_lattice3('#skF_6', k16_lattice3('#skF_6', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_4509])).
% 8.84/2.98  tff(c_4918, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_4915, c_4519])).
% 8.84/2.98  tff(c_4922, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_4918])).
% 8.84/2.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.84/2.98  
% 8.84/2.98  Inference rules
% 8.84/2.98  ----------------------
% 8.84/2.98  #Ref     : 0
% 8.84/2.98  #Sup     : 1061
% 8.84/2.98  #Fact    : 0
% 8.84/2.98  #Define  : 0
% 8.84/2.98  #Split   : 13
% 8.84/2.98  #Chain   : 0
% 8.84/2.98  #Close   : 0
% 8.84/2.98  
% 8.84/2.98  Ordering : KBO
% 8.84/2.98  
% 8.84/2.98  Simplification rules
% 8.84/2.98  ----------------------
% 8.84/2.98  #Subsume      : 168
% 8.84/2.98  #Demod        : 640
% 8.84/2.98  #Tautology    : 106
% 8.84/2.98  #SimpNegUnit  : 222
% 8.84/2.98  #BackRed      : 0
% 8.84/2.98  
% 8.84/2.98  #Partial instantiations: 0
% 8.84/2.98  #Strategies tried      : 1
% 8.84/2.98  
% 8.84/2.98  Timing (in seconds)
% 8.84/2.98  ----------------------
% 8.84/2.98  Preprocessing        : 0.32
% 8.84/2.98  Parsing              : 0.18
% 8.84/2.98  CNF conversion       : 0.03
% 8.84/2.98  Main loop            : 1.87
% 8.84/2.98  Inferencing          : 0.68
% 8.84/2.98  Reduction            : 0.44
% 8.84/2.98  Demodulation         : 0.28
% 8.84/2.98  BG Simplification    : 0.06
% 8.84/2.98  Subsumption          : 0.57
% 8.84/2.98  Abstraction          : 0.08
% 8.84/2.98  MUC search           : 0.00
% 8.84/2.98  Cooper               : 0.00
% 8.84/2.98  Total                : 2.24
% 8.84/2.98  Index Insertion      : 0.00
% 8.84/2.98  Index Deletion       : 0.00
% 8.84/2.98  Index Matching       : 0.00
% 8.84/2.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
