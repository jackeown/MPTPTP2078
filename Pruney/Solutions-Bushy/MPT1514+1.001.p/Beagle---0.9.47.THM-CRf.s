%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1514+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:59 EST 2020

% Result     : Theorem 5.09s
% Output     : CNFRefutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :  166 (3747 expanded)
%              Number of leaves         :   38 (1309 expanded)
%              Depth                    :   36
%              Number of atoms          :  600 (21305 expanded)
%              Number of equality atoms :    1 (  23 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

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

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_192,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B,C] :
            ( ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ~ ( r2_hidden(D,B)
                    & ! [E] :
                        ( m1_subset_1(E,u1_struct_0(A))
                       => ~ ( r3_lattices(A,D,E)
                            & r2_hidden(E,C) ) ) ) )
           => r3_lattices(A,k15_lattice3(A,B),k15_lattice3(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_165,axiom,(
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

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B,C] :
            ( m1_subset_1(C,u1_struct_0(A))
           => ( C = k15_lattice3(A,B)
            <=> ( r4_lattice3(A,C,B)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r4_lattice3(A,D,B)
                     => r1_lattices(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

tff(f_46,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_lattices(A,B,C)
      <=> r1_lattices(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(f_64,axiom,(
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

tff(f_105,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_146,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_lattices(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_lattices(A,B,C)
                      & r1_lattices(A,C,D) )
                   => r1_lattices(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_lattices)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_52,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_34,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(k15_lattice3(A_36,B_37),u1_struct_0(A_36))
      | ~ l3_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_56,plain,(
    v10_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_54,plain,(
    v4_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_93,plain,(
    ! [A_103,B_104,C_105] :
      ( r3_lattices(A_103,B_104,k15_lattice3(A_103,C_105))
      | ~ r2_hidden(B_104,C_105)
      | ~ m1_subset_1(B_104,u1_struct_0(A_103))
      | ~ l3_lattices(A_103)
      | ~ v4_lattice3(A_103)
      | ~ v10_lattices(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_50,plain,(
    ~ r3_lattices('#skF_3',k15_lattice3('#skF_3','#skF_4'),k15_lattice3('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_96,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_3','#skF_4'),'#skF_5')
    | ~ m1_subset_1(k15_lattice3('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | ~ v4_lattice3('#skF_3')
    | ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_50])).

tff(c_99,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_3','#skF_4'),'#skF_5')
    | ~ m1_subset_1(k15_lattice3('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_96])).

tff(c_100,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_3','#skF_4'),'#skF_5')
    | ~ m1_subset_1(k15_lattice3('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_99])).

tff(c_102,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_105,plain,
    ( ~ l3_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_102])).

tff(c_108,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_105])).

tff(c_110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_108])).

tff(c_112,plain,(
    m1_subset_1(k15_lattice3('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_243,plain,(
    ! [A_141,B_142,D_143] :
      ( r1_lattices(A_141,k15_lattice3(A_141,B_142),D_143)
      | ~ r4_lattice3(A_141,D_143,B_142)
      | ~ m1_subset_1(D_143,u1_struct_0(A_141))
      | ~ m1_subset_1(k15_lattice3(A_141,B_142),u1_struct_0(A_141))
      | ~ v4_lattice3(A_141)
      | ~ v10_lattices(A_141)
      | ~ l3_lattices(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_245,plain,(
    ! [D_143] :
      ( r1_lattices('#skF_3',k15_lattice3('#skF_3','#skF_4'),D_143)
      | ~ r4_lattice3('#skF_3',D_143,'#skF_4')
      | ~ m1_subset_1(D_143,u1_struct_0('#skF_3'))
      | ~ v4_lattice3('#skF_3')
      | ~ v10_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_112,c_243])).

tff(c_250,plain,(
    ! [D_143] :
      ( r1_lattices('#skF_3',k15_lattice3('#skF_3','#skF_4'),D_143)
      | ~ r4_lattice3('#skF_3',D_143,'#skF_4')
      | ~ m1_subset_1(D_143,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_54,c_245])).

tff(c_253,plain,(
    ! [D_144] :
      ( r1_lattices('#skF_3',k15_lattice3('#skF_3','#skF_4'),D_144)
      | ~ r4_lattice3('#skF_3',D_144,'#skF_4')
      | ~ m1_subset_1(D_144,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_250])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_62,plain,(
    ! [D_75] :
      ( r3_lattices('#skF_3',D_75,'#skF_6'(D_75))
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_120,plain,(
    ! [A_113,B_114,C_115] :
      ( r1_lattices(A_113,B_114,C_115)
      | ~ r3_lattices(A_113,B_114,C_115)
      | ~ m1_subset_1(C_115,u1_struct_0(A_113))
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l3_lattices(A_113)
      | ~ v9_lattices(A_113)
      | ~ v8_lattices(A_113)
      | ~ v6_lattices(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_126,plain,(
    ! [D_75] :
      ( r1_lattices('#skF_3',D_75,'#skF_6'(D_75))
      | ~ m1_subset_1('#skF_6'(D_75),u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_62,c_120])).

tff(c_131,plain,(
    ! [D_75] :
      ( r1_lattices('#skF_3',D_75,'#skF_6'(D_75))
      | ~ m1_subset_1('#skF_6'(D_75),u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_126])).

tff(c_132,plain,(
    ! [D_75] :
      ( r1_lattices('#skF_3',D_75,'#skF_6'(D_75))
      | ~ m1_subset_1('#skF_6'(D_75),u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_131])).

tff(c_133,plain,(
    ~ v6_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_136,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_133])).

tff(c_139,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_136])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_139])).

tff(c_143,plain,(
    v6_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_144,plain,(
    ! [A_116,B_117,C_118] :
      ( r3_lattices(A_116,B_117,C_118)
      | ~ r1_lattices(A_116,B_117,C_118)
      | ~ m1_subset_1(C_118,u1_struct_0(A_116))
      | ~ m1_subset_1(B_117,u1_struct_0(A_116))
      | ~ l3_lattices(A_116)
      | ~ v9_lattices(A_116)
      | ~ v8_lattices(A_116)
      | ~ v6_lattices(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_146,plain,(
    ! [B_117] :
      ( r3_lattices('#skF_3',B_117,k15_lattice3('#skF_3','#skF_4'))
      | ~ r1_lattices('#skF_3',B_117,k15_lattice3('#skF_3','#skF_4'))
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_112,c_144])).

tff(c_155,plain,(
    ! [B_117] :
      ( r3_lattices('#skF_3',B_117,k15_lattice3('#skF_3','#skF_4'))
      | ~ r1_lattices('#skF_3',B_117,k15_lattice3('#skF_3','#skF_4'))
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_52,c_146])).

tff(c_156,plain,(
    ! [B_117] :
      ( r3_lattices('#skF_3',B_117,k15_lattice3('#skF_3','#skF_4'))
      | ~ r1_lattices('#skF_3',B_117,k15_lattice3('#skF_3','#skF_4'))
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_155])).

tff(c_163,plain,(
    ~ v8_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_166,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_163])).

tff(c_169,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_166])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_169])).

tff(c_173,plain,(
    v8_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,(
    ! [D_75] :
      ( m1_subset_1('#skF_6'(D_75),u1_struct_0('#skF_3'))
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_150,plain,(
    ! [B_117,D_75] :
      ( r3_lattices('#skF_3',B_117,'#skF_6'(D_75))
      | ~ r1_lattices('#skF_3',B_117,'#skF_6'(D_75))
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_64,c_144])).

tff(c_160,plain,(
    ! [B_117,D_75] :
      ( r3_lattices('#skF_3',B_117,'#skF_6'(D_75))
      | ~ r1_lattices('#skF_3',B_117,'#skF_6'(D_75))
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_52,c_150])).

tff(c_161,plain,(
    ! [B_117,D_75] :
      ( r3_lattices('#skF_3',B_117,'#skF_6'(D_75))
      | ~ r1_lattices('#skF_3',B_117,'#skF_6'(D_75))
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_160])).

tff(c_175,plain,(
    ! [B_117,D_75] :
      ( r3_lattices('#skF_3',B_117,'#skF_6'(D_75))
      | ~ r1_lattices('#skF_3',B_117,'#skF_6'(D_75))
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3')
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_161])).

tff(c_176,plain,(
    ~ v9_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_179,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_176])).

tff(c_182,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_179])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_182])).

tff(c_186,plain,(
    v9_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_211,plain,(
    ! [A_127,B_128,B_129] :
      ( r3_lattices(A_127,B_128,k15_lattice3(A_127,B_129))
      | ~ r1_lattices(A_127,B_128,k15_lattice3(A_127,B_129))
      | ~ m1_subset_1(B_128,u1_struct_0(A_127))
      | ~ v9_lattices(A_127)
      | ~ v8_lattices(A_127)
      | ~ v6_lattices(A_127)
      | ~ l3_lattices(A_127)
      | v2_struct_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_34,c_144])).

tff(c_216,plain,
    ( ~ r1_lattices('#skF_3',k15_lattice3('#skF_3','#skF_4'),k15_lattice3('#skF_3','#skF_5'))
    | ~ m1_subset_1(k15_lattice3('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | ~ v9_lattices('#skF_3')
    | ~ v8_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | ~ l3_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_211,c_50])).

tff(c_220,plain,
    ( ~ r1_lattices('#skF_3',k15_lattice3('#skF_3','#skF_4'),k15_lattice3('#skF_3','#skF_5'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_143,c_173,c_186,c_112,c_216])).

tff(c_221,plain,(
    ~ r1_lattices('#skF_3',k15_lattice3('#skF_3','#skF_4'),k15_lattice3('#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_220])).

tff(c_265,plain,
    ( ~ r4_lattice3('#skF_3',k15_lattice3('#skF_3','#skF_5'),'#skF_4')
    | ~ m1_subset_1(k15_lattice3('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_253,c_221])).

tff(c_285,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_288,plain,
    ( ~ l3_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_285])).

tff(c_291,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_288])).

tff(c_293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_291])).

tff(c_294,plain,(
    ~ r4_lattice3('#skF_3',k15_lattice3('#skF_3','#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_295,plain,(
    m1_subset_1(k15_lattice3('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_20,plain,(
    ! [A_2,B_14,C_20] :
      ( r2_hidden('#skF_1'(A_2,B_14,C_20),C_20)
      | r4_lattice3(A_2,B_14,C_20)
      | ~ m1_subset_1(B_14,u1_struct_0(A_2))
      | ~ l3_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [A_2,B_14,C_20] :
      ( m1_subset_1('#skF_1'(A_2,B_14,C_20),u1_struct_0(A_2))
      | r4_lattice3(A_2,B_14,C_20)
      | ~ m1_subset_1(B_14,u1_struct_0(A_2))
      | ~ l3_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_88,plain,(
    ! [A_99,B_100] :
      ( r4_lattice3(A_99,k15_lattice3(A_99,B_100),B_100)
      | ~ m1_subset_1(k15_lattice3(A_99,B_100),u1_struct_0(A_99))
      | ~ v4_lattice3(A_99)
      | ~ v10_lattices(A_99)
      | ~ l3_lattices(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_91,plain,(
    ! [A_36,B_37] :
      ( r4_lattice3(A_36,k15_lattice3(A_36,B_37),B_37)
      | ~ v4_lattice3(A_36)
      | ~ v10_lattices(A_36)
      | ~ l3_lattices(A_36)
      | v2_struct_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_34,c_88])).

tff(c_30,plain,(
    ! [A_24,B_31,D_35] :
      ( r1_lattices(A_24,k15_lattice3(A_24,B_31),D_35)
      | ~ r4_lattice3(A_24,D_35,B_31)
      | ~ m1_subset_1(D_35,u1_struct_0(A_24))
      | ~ m1_subset_1(k15_lattice3(A_24,B_31),u1_struct_0(A_24))
      | ~ v4_lattice3(A_24)
      | ~ v10_lattices(A_24)
      | ~ l3_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_308,plain,(
    ! [D_35] :
      ( r1_lattices('#skF_3',k15_lattice3('#skF_3','#skF_5'),D_35)
      | ~ r4_lattice3('#skF_3',D_35,'#skF_5')
      | ~ m1_subset_1(D_35,u1_struct_0('#skF_3'))
      | ~ v4_lattice3('#skF_3')
      | ~ v10_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_295,c_30])).

tff(c_313,plain,(
    ! [D_35] :
      ( r1_lattices('#skF_3',k15_lattice3('#skF_3','#skF_5'),D_35)
      | ~ r4_lattice3('#skF_3',D_35,'#skF_5')
      | ~ m1_subset_1(D_35,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_54,c_308])).

tff(c_314,plain,(
    ! [D_35] :
      ( r1_lattices('#skF_3',k15_lattice3('#skF_3','#skF_5'),D_35)
      | ~ r4_lattice3('#skF_3',D_35,'#skF_5')
      | ~ m1_subset_1(D_35,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_313])).

tff(c_10,plain,(
    ! [A_1] :
      ( v5_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,(
    ! [A_78] :
      ( l2_lattices(A_78)
      | ~ l3_lattices(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_74,plain,(
    l2_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_70])).

tff(c_251,plain,(
    ! [D_143] :
      ( r1_lattices('#skF_3',k15_lattice3('#skF_3','#skF_4'),D_143)
      | ~ r4_lattice3('#skF_3',D_143,'#skF_4')
      | ~ m1_subset_1(D_143,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_250])).

tff(c_266,plain,(
    ! [A_145,B_146,D_147,C_148] :
      ( r1_lattices(A_145,B_146,D_147)
      | ~ r1_lattices(A_145,C_148,D_147)
      | ~ r1_lattices(A_145,B_146,C_148)
      | ~ m1_subset_1(D_147,u1_struct_0(A_145))
      | ~ m1_subset_1(C_148,u1_struct_0(A_145))
      | ~ m1_subset_1(B_146,u1_struct_0(A_145))
      | ~ l2_lattices(A_145)
      | ~ v5_lattices(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_268,plain,(
    ! [B_146,D_143] :
      ( r1_lattices('#skF_3',B_146,D_143)
      | ~ r1_lattices('#skF_3',B_146,k15_lattice3('#skF_3','#skF_4'))
      | ~ m1_subset_1(k15_lattice3('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v5_lattices('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r4_lattice3('#skF_3',D_143,'#skF_4')
      | ~ m1_subset_1(D_143,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_251,c_266])).

tff(c_275,plain,(
    ! [B_146,D_143] :
      ( r1_lattices('#skF_3',B_146,D_143)
      | ~ r1_lattices('#skF_3',B_146,k15_lattice3('#skF_3','#skF_4'))
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_3'))
      | ~ v5_lattices('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r4_lattice3('#skF_3',D_143,'#skF_4')
      | ~ m1_subset_1(D_143,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_112,c_268])).

tff(c_276,plain,(
    ! [B_146,D_143] :
      ( r1_lattices('#skF_3',B_146,D_143)
      | ~ r1_lattices('#skF_3',B_146,k15_lattice3('#skF_3','#skF_4'))
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_3'))
      | ~ v5_lattices('#skF_3')
      | ~ r4_lattice3('#skF_3',D_143,'#skF_4')
      | ~ m1_subset_1(D_143,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_275])).

tff(c_296,plain,(
    ~ v5_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_299,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_296])).

tff(c_302,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_299])).

tff(c_304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_302])).

tff(c_306,plain,(
    v5_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_48,plain,(
    ! [A_57,B_61,C_63] :
      ( r3_lattices(A_57,B_61,k15_lattice3(A_57,C_63))
      | ~ r2_hidden(B_61,C_63)
      | ~ m1_subset_1(B_61,u1_struct_0(A_57))
      | ~ l3_lattices(A_57)
      | ~ v4_lattice3(A_57)
      | ~ v10_lattices(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_466,plain,(
    ! [A_168,B_169,C_170] :
      ( r1_lattices(A_168,B_169,k15_lattice3(A_168,C_170))
      | ~ m1_subset_1(k15_lattice3(A_168,C_170),u1_struct_0(A_168))
      | ~ v9_lattices(A_168)
      | ~ v8_lattices(A_168)
      | ~ v6_lattices(A_168)
      | ~ r2_hidden(B_169,C_170)
      | ~ m1_subset_1(B_169,u1_struct_0(A_168))
      | ~ l3_lattices(A_168)
      | ~ v4_lattice3(A_168)
      | ~ v10_lattices(A_168)
      | v2_struct_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_48,c_120])).

tff(c_468,plain,(
    ! [B_169] :
      ( r1_lattices('#skF_3',B_169,k15_lattice3('#skF_3','#skF_5'))
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | ~ r2_hidden(B_169,'#skF_5')
      | ~ m1_subset_1(B_169,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v4_lattice3('#skF_3')
      | ~ v10_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_295,c_466])).

tff(c_475,plain,(
    ! [B_169] :
      ( r1_lattices('#skF_3',B_169,k15_lattice3('#skF_3','#skF_5'))
      | ~ r2_hidden(B_169,'#skF_5')
      | ~ m1_subset_1(B_169,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_143,c_173,c_186,c_468])).

tff(c_500,plain,(
    ! [B_172] :
      ( r1_lattices('#skF_3',B_172,k15_lattice3('#skF_3','#skF_5'))
      | ~ r2_hidden(B_172,'#skF_5')
      | ~ m1_subset_1(B_172,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_475])).

tff(c_44,plain,(
    ! [A_42,B_50,D_56,C_54] :
      ( r1_lattices(A_42,B_50,D_56)
      | ~ r1_lattices(A_42,C_54,D_56)
      | ~ r1_lattices(A_42,B_50,C_54)
      | ~ m1_subset_1(D_56,u1_struct_0(A_42))
      | ~ m1_subset_1(C_54,u1_struct_0(A_42))
      | ~ m1_subset_1(B_50,u1_struct_0(A_42))
      | ~ l2_lattices(A_42)
      | ~ v5_lattices(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_504,plain,(
    ! [B_50,B_172] :
      ( r1_lattices('#skF_3',B_50,k15_lattice3('#skF_3','#skF_5'))
      | ~ r1_lattices('#skF_3',B_50,B_172)
      | ~ m1_subset_1(k15_lattice3('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v5_lattices('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(B_172,'#skF_5')
      | ~ m1_subset_1(B_172,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_500,c_44])).

tff(c_515,plain,(
    ! [B_50,B_172] :
      ( r1_lattices('#skF_3',B_50,k15_lattice3('#skF_3','#skF_5'))
      | ~ r1_lattices('#skF_3',B_50,B_172)
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(B_172,'#skF_5')
      | ~ m1_subset_1(B_172,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_74,c_295,c_504])).

tff(c_756,plain,(
    ! [B_198,B_199] :
      ( r1_lattices('#skF_3',B_198,k15_lattice3('#skF_3','#skF_5'))
      | ~ r1_lattices('#skF_3',B_198,B_199)
      | ~ m1_subset_1(B_198,u1_struct_0('#skF_3'))
      | ~ r2_hidden(B_199,'#skF_5')
      | ~ m1_subset_1(B_199,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_515])).

tff(c_767,plain,(
    ! [D_35] :
      ( r1_lattices('#skF_3',k15_lattice3('#skF_3','#skF_5'),k15_lattice3('#skF_3','#skF_5'))
      | ~ m1_subset_1(k15_lattice3('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
      | ~ r2_hidden(D_35,'#skF_5')
      | ~ r4_lattice3('#skF_3',D_35,'#skF_5')
      | ~ m1_subset_1(D_35,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_314,c_756])).

tff(c_787,plain,(
    ! [D_35] :
      ( r1_lattices('#skF_3',k15_lattice3('#skF_3','#skF_5'),k15_lattice3('#skF_3','#skF_5'))
      | ~ r2_hidden(D_35,'#skF_5')
      | ~ r4_lattice3('#skF_3',D_35,'#skF_5')
      | ~ m1_subset_1(D_35,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_767])).

tff(c_843,plain,(
    ! [D_205] :
      ( ~ r2_hidden(D_205,'#skF_5')
      | ~ r4_lattice3('#skF_3',D_205,'#skF_5')
      | ~ m1_subset_1(D_205,u1_struct_0('#skF_3')) ) ),
    inference(splitLeft,[status(thm)],[c_787])).

tff(c_865,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_3','#skF_5'),'#skF_5')
    | ~ r4_lattice3('#skF_3',k15_lattice3('#skF_3','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_295,c_843])).

tff(c_884,plain,(
    ~ r4_lattice3('#skF_3',k15_lattice3('#skF_3','#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_865])).

tff(c_887,plain,
    ( ~ v4_lattice3('#skF_3')
    | ~ v10_lattices('#skF_3')
    | ~ l3_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_91,c_884])).

tff(c_890,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_54,c_887])).

tff(c_892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_890])).

tff(c_894,plain,(
    r4_lattice3('#skF_3',k15_lattice3('#skF_3','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_865])).

tff(c_142,plain,(
    ! [D_75] :
      ( ~ v8_lattices('#skF_3')
      | ~ v9_lattices('#skF_3')
      | r1_lattices('#skF_3',D_75,'#skF_6'(D_75))
      | ~ m1_subset_1('#skF_6'(D_75),u1_struct_0('#skF_3'))
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_198,plain,(
    ! [D_120] :
      ( r1_lattices('#skF_3',D_120,'#skF_6'(D_120))
      | ~ m1_subset_1('#skF_6'(D_120),u1_struct_0('#skF_3'))
      | ~ r2_hidden(D_120,'#skF_4')
      | ~ m1_subset_1(D_120,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_173,c_142])).

tff(c_201,plain,(
    ! [D_75] :
      ( r1_lattices('#skF_3',D_75,'#skF_6'(D_75))
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_64,c_198])).

tff(c_60,plain,(
    ! [D_75] :
      ( r2_hidden('#skF_6'(D_75),'#skF_5')
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_113,plain,(
    ! [A_109,D_110,B_111,C_112] :
      ( r1_lattices(A_109,D_110,B_111)
      | ~ r2_hidden(D_110,C_112)
      | ~ m1_subset_1(D_110,u1_struct_0(A_109))
      | ~ r4_lattice3(A_109,B_111,C_112)
      | ~ m1_subset_1(B_111,u1_struct_0(A_109))
      | ~ l3_lattices(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_222,plain,(
    ! [A_130,D_131,B_132] :
      ( r1_lattices(A_130,'#skF_6'(D_131),B_132)
      | ~ m1_subset_1('#skF_6'(D_131),u1_struct_0(A_130))
      | ~ r4_lattice3(A_130,B_132,'#skF_5')
      | ~ m1_subset_1(B_132,u1_struct_0(A_130))
      | ~ l3_lattices(A_130)
      | v2_struct_0(A_130)
      | ~ r2_hidden(D_131,'#skF_4')
      | ~ m1_subset_1(D_131,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_60,c_113])).

tff(c_224,plain,(
    ! [D_75,B_132] :
      ( r1_lattices('#skF_3','#skF_6'(D_75),B_132)
      | ~ r4_lattice3('#skF_3',B_132,'#skF_5')
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_64,c_222])).

tff(c_227,plain,(
    ! [D_75,B_132] :
      ( r1_lattices('#skF_3','#skF_6'(D_75),B_132)
      | ~ r4_lattice3('#skF_3',B_132,'#skF_5')
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_224])).

tff(c_228,plain,(
    ! [D_75,B_132] :
      ( r1_lattices('#skF_3','#skF_6'(D_75),B_132)
      | ~ r4_lattice3('#skF_3',B_132,'#skF_5')
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_3'))
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_227])).

tff(c_270,plain,(
    ! [B_146,B_132,D_75] :
      ( r1_lattices('#skF_3',B_146,B_132)
      | ~ r1_lattices('#skF_3',B_146,'#skF_6'(D_75))
      | ~ m1_subset_1('#skF_6'(D_75),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | ~ v5_lattices('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r4_lattice3('#skF_3',B_132,'#skF_5')
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_3'))
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_228,c_266])).

tff(c_279,plain,(
    ! [B_146,B_132,D_75] :
      ( r1_lattices('#skF_3',B_146,B_132)
      | ~ r1_lattices('#skF_3',B_146,'#skF_6'(D_75))
      | ~ m1_subset_1('#skF_6'(D_75),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_3'))
      | ~ v5_lattices('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r4_lattice3('#skF_3',B_132,'#skF_5')
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_3'))
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_270])).

tff(c_280,plain,(
    ! [B_146,B_132,D_75] :
      ( r1_lattices('#skF_3',B_146,B_132)
      | ~ r1_lattices('#skF_3',B_146,'#skF_6'(D_75))
      | ~ m1_subset_1('#skF_6'(D_75),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_3'))
      | ~ v5_lattices('#skF_3')
      | ~ r4_lattice3('#skF_3',B_132,'#skF_5')
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_3'))
      | ~ r2_hidden(D_75,'#skF_4')
      | ~ m1_subset_1(D_75,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_279])).

tff(c_1937,plain,(
    ! [B_318,B_319,D_320] :
      ( r1_lattices('#skF_3',B_318,B_319)
      | ~ r1_lattices('#skF_3',B_318,'#skF_6'(D_320))
      | ~ m1_subset_1('#skF_6'(D_320),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_318,u1_struct_0('#skF_3'))
      | ~ r4_lattice3('#skF_3',B_319,'#skF_5')
      | ~ m1_subset_1(B_319,u1_struct_0('#skF_3'))
      | ~ r2_hidden(D_320,'#skF_4')
      | ~ m1_subset_1(D_320,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_280])).

tff(c_1988,plain,(
    ! [D_322,B_323] :
      ( r1_lattices('#skF_3',D_322,B_323)
      | ~ m1_subset_1('#skF_6'(D_322),u1_struct_0('#skF_3'))
      | ~ r4_lattice3('#skF_3',B_323,'#skF_5')
      | ~ m1_subset_1(B_323,u1_struct_0('#skF_3'))
      | ~ r2_hidden(D_322,'#skF_4')
      | ~ m1_subset_1(D_322,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_201,c_1937])).

tff(c_1992,plain,(
    ! [D_324,B_325] :
      ( r1_lattices('#skF_3',D_324,B_325)
      | ~ r4_lattice3('#skF_3',B_325,'#skF_5')
      | ~ m1_subset_1(B_325,u1_struct_0('#skF_3'))
      | ~ r2_hidden(D_324,'#skF_4')
      | ~ m1_subset_1(D_324,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_64,c_1988])).

tff(c_1994,plain,(
    ! [D_324] :
      ( r1_lattices('#skF_3',D_324,k15_lattice3('#skF_3','#skF_5'))
      | ~ r4_lattice3('#skF_3',k15_lattice3('#skF_3','#skF_5'),'#skF_5')
      | ~ r2_hidden(D_324,'#skF_4')
      | ~ m1_subset_1(D_324,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_295,c_1992])).

tff(c_2036,plain,(
    ! [D_328] :
      ( r1_lattices('#skF_3',D_328,k15_lattice3('#skF_3','#skF_5'))
      | ~ r2_hidden(D_328,'#skF_4')
      | ~ m1_subset_1(D_328,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_1994])).

tff(c_18,plain,(
    ! [A_2,B_14,C_20] :
      ( ~ r1_lattices(A_2,'#skF_1'(A_2,B_14,C_20),B_14)
      | r4_lattice3(A_2,B_14,C_20)
      | ~ m1_subset_1(B_14,u1_struct_0(A_2))
      | ~ l3_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2059,plain,(
    ! [C_20] :
      ( r4_lattice3('#skF_3',k15_lattice3('#skF_3','#skF_5'),C_20)
      | ~ m1_subset_1(k15_lattice3('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',k15_lattice3('#skF_3','#skF_5'),C_20),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3',k15_lattice3('#skF_3','#skF_5'),C_20),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2036,c_18])).

tff(c_2089,plain,(
    ! [C_20] :
      ( r4_lattice3('#skF_3',k15_lattice3('#skF_3','#skF_5'),C_20)
      | v2_struct_0('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',k15_lattice3('#skF_3','#skF_5'),C_20),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3',k15_lattice3('#skF_3','#skF_5'),C_20),u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_295,c_2059])).

tff(c_2162,plain,(
    ! [C_331] :
      ( r4_lattice3('#skF_3',k15_lattice3('#skF_3','#skF_5'),C_331)
      | ~ r2_hidden('#skF_1'('#skF_3',k15_lattice3('#skF_3','#skF_5'),C_331),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3',k15_lattice3('#skF_3','#skF_5'),C_331),u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2089])).

tff(c_2166,plain,(
    ! [C_20] :
      ( ~ r2_hidden('#skF_1'('#skF_3',k15_lattice3('#skF_3','#skF_5'),C_20),'#skF_4')
      | r4_lattice3('#skF_3',k15_lattice3('#skF_3','#skF_5'),C_20)
      | ~ m1_subset_1(k15_lattice3('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_2162])).

tff(c_2169,plain,(
    ! [C_20] :
      ( ~ r2_hidden('#skF_1'('#skF_3',k15_lattice3('#skF_3','#skF_5'),C_20),'#skF_4')
      | r4_lattice3('#skF_3',k15_lattice3('#skF_3','#skF_5'),C_20)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_295,c_2166])).

tff(c_2175,plain,(
    ! [C_335] :
      ( ~ r2_hidden('#skF_1'('#skF_3',k15_lattice3('#skF_3','#skF_5'),C_335),'#skF_4')
      | r4_lattice3('#skF_3',k15_lattice3('#skF_3','#skF_5'),C_335) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2169])).

tff(c_2179,plain,
    ( r4_lattice3('#skF_3',k15_lattice3('#skF_3','#skF_5'),'#skF_4')
    | ~ m1_subset_1(k15_lattice3('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
    | ~ l3_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_2175])).

tff(c_2182,plain,
    ( r4_lattice3('#skF_3',k15_lattice3('#skF_3','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_295,c_2179])).

tff(c_2184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_294,c_2182])).

%------------------------------------------------------------------------------
