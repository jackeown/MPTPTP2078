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
% DateTime   : Thu Dec  3 10:20:17 EST 2020

% Result     : Theorem 5.69s
% Output     : CNFRefutation 5.78s
% Verified   : 
% Statistics : Number of formulae       :  182 (2326 expanded)
%              Number of leaves         :   46 ( 791 expanded)
%              Depth                    :   23
%              Number of atoms          :  529 (8294 expanded)
%              Number of equality atoms :   60 (1259 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_5 > #skF_2 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k6_lattices,type,(
    k6_lattices: $i > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v14_lattices,type,(
    v14_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_270,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v14_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k4_lattices(A,k6_lattices(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).

tff(f_47,axiom,(
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

tff(f_123,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_117,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => m1_subset_1(k6_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ( v14_lattices(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( B = k6_lattices(A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( k1_lattices(A,B,C) = B
                    & k1_lattices(A,C,B) = B ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattices)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ( v5_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => k1_lattices(A,B,k1_lattices(A,C,D)) = k1_lattices(A,k1_lattices(A,B,C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattices)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v8_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k1_lattices(A,k2_lattices(A,B,C),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

tff(f_172,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_lattices(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

tff(f_212,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_lattices(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => r1_lattices(A,B,k1_lattices(A,B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_lattices)).

tff(f_191,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k2_lattices(A,B,C) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

tff(f_155,axiom,(
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

tff(f_255,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_lattices(A,B,C)
                   => r1_lattices(A,k2_lattices(A,B,D),k2_lattices(A,C,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_lattices)).

tff(f_231,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_lattices(A,B,C)
                  & r1_lattices(A,C,B) )
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k2_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_72,plain,(
    l3_lattices('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_76,plain,(
    v10_lattices('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_10,plain,(
    ! [A_1] :
      ( v5_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_84,plain,(
    ! [A_101] :
      ( l2_lattices(A_101)
      | ~ l3_lattices(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_88,plain,(
    l2_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_84])).

tff(c_44,plain,(
    ! [A_52] :
      ( m1_subset_1(k6_lattices(A_52),u1_struct_0(A_52))
      | ~ l2_lattices(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_74,plain,(
    v14_lattices('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_225,plain,(
    ! [A_124,C_125] :
      ( k1_lattices(A_124,k6_lattices(A_124),C_125) = k6_lattices(A_124)
      | ~ m1_subset_1(C_125,u1_struct_0(A_124))
      | ~ m1_subset_1(k6_lattices(A_124),u1_struct_0(A_124))
      | ~ v14_lattices(A_124)
      | ~ l2_lattices(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_243,plain,
    ( k1_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8') = k6_lattices('#skF_7')
    | ~ m1_subset_1(k6_lattices('#skF_7'),u1_struct_0('#skF_7'))
    | ~ v14_lattices('#skF_7')
    | ~ l2_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_225])).

tff(c_254,plain,
    ( k1_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8') = k6_lattices('#skF_7')
    | ~ m1_subset_1(k6_lattices('#skF_7'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_74,c_243])).

tff(c_255,plain,
    ( k1_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8') = k6_lattices('#skF_7')
    | ~ m1_subset_1(k6_lattices('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_254])).

tff(c_256,plain,(
    ~ m1_subset_1(k6_lattices('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_259,plain,
    ( ~ l2_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_256])).

tff(c_262,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_259])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_262])).

tff(c_266,plain,(
    m1_subset_1(k6_lattices('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_28,plain,(
    ! [A_12] :
      ( m1_subset_1('#skF_4'(A_12),u1_struct_0(A_12))
      | v5_lattices(A_12)
      | ~ l2_lattices(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_79,plain,(
    ! [A_100] :
      ( l1_lattices(A_100)
      | ~ l3_lattices(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_83,plain,(
    l1_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_79])).

tff(c_104,plain,(
    ! [A_120,B_121,C_122] :
      ( k4_lattices(A_120,B_121,C_122) = k2_lattices(A_120,B_121,C_122)
      | ~ m1_subset_1(C_122,u1_struct_0(A_120))
      | ~ m1_subset_1(B_121,u1_struct_0(A_120))
      | ~ l1_lattices(A_120)
      | ~ v6_lattices(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_122,plain,(
    ! [B_121] :
      ( k4_lattices('#skF_7',B_121,'#skF_8') = k2_lattices('#skF_7',B_121,'#skF_8')
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_7'))
      | ~ l1_lattices('#skF_7')
      | ~ v6_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_104])).

tff(c_133,plain,(
    ! [B_121] :
      ( k4_lattices('#skF_7',B_121,'#skF_8') = k2_lattices('#skF_7',B_121,'#skF_8')
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_7'))
      | ~ v6_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_122])).

tff(c_134,plain,(
    ! [B_121] :
      ( k4_lattices('#skF_7',B_121,'#skF_8') = k2_lattices('#skF_7',B_121,'#skF_8')
      | ~ m1_subset_1(B_121,u1_struct_0('#skF_7'))
      | ~ v6_lattices('#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_133])).

tff(c_135,plain,(
    ~ v6_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_138,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_8,c_135])).

tff(c_141,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_138])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_141])).

tff(c_146,plain,(
    ! [B_123] :
      ( k4_lattices('#skF_7',B_123,'#skF_8') = k2_lattices('#skF_7',B_123,'#skF_8')
      | ~ m1_subset_1(B_123,u1_struct_0('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_162,plain,
    ( k4_lattices('#skF_7','#skF_4'('#skF_7'),'#skF_8') = k2_lattices('#skF_7','#skF_4'('#skF_7'),'#skF_8')
    | v5_lattices('#skF_7')
    | ~ l2_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_146])).

tff(c_196,plain,
    ( k4_lattices('#skF_7','#skF_4'('#skF_7'),'#skF_8') = k2_lattices('#skF_7','#skF_4'('#skF_7'),'#skF_8')
    | v5_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_162])).

tff(c_197,plain,
    ( k4_lattices('#skF_7','#skF_4'('#skF_7'),'#skF_8') = k2_lattices('#skF_7','#skF_4'('#skF_7'),'#skF_8')
    | v5_lattices('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_196])).

tff(c_224,plain,(
    v5_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_145,plain,(
    v6_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_38,plain,(
    ! [A_38] :
      ( m1_subset_1('#skF_6'(A_38),u1_struct_0(A_38))
      | v8_lattices(A_38)
      | ~ l3_lattices(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_166,plain,
    ( k4_lattices('#skF_7','#skF_6'('#skF_7'),'#skF_8') = k2_lattices('#skF_7','#skF_6'('#skF_7'),'#skF_8')
    | v8_lattices('#skF_7')
    | ~ l3_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_146])).

tff(c_200,plain,
    ( k4_lattices('#skF_7','#skF_6'('#skF_7'),'#skF_8') = k2_lattices('#skF_7','#skF_6'('#skF_7'),'#skF_8')
    | v8_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_166])).

tff(c_201,plain,
    ( k4_lattices('#skF_7','#skF_6'('#skF_7'),'#skF_8') = k2_lattices('#skF_7','#skF_6'('#skF_7'),'#skF_8')
    | v8_lattices('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_200])).

tff(c_292,plain,(
    v8_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_295,plain,(
    ! [A_126,B_127,C_128] :
      ( r3_lattices(A_126,B_127,B_127)
      | ~ m1_subset_1(C_128,u1_struct_0(A_126))
      | ~ m1_subset_1(B_127,u1_struct_0(A_126))
      | ~ l3_lattices(A_126)
      | ~ v9_lattices(A_126)
      | ~ v8_lattices(A_126)
      | ~ v6_lattices(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_297,plain,(
    ! [B_127] :
      ( r3_lattices('#skF_7',B_127,B_127)
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v9_lattices('#skF_7')
      | ~ v8_lattices('#skF_7')
      | ~ v6_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_266,c_295])).

tff(c_318,plain,(
    ! [B_127] :
      ( r3_lattices('#skF_7',B_127,B_127)
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_7'))
      | ~ v9_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_292,c_72,c_297])).

tff(c_319,plain,(
    ! [B_127] :
      ( r3_lattices('#skF_7',B_127,B_127)
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_7'))
      | ~ v9_lattices('#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_318])).

tff(c_332,plain,(
    ~ v9_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_335,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_2,c_332])).

tff(c_338,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_335])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_338])).

tff(c_342,plain,(
    v9_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_410,plain,(
    ! [A_130,C_131] :
      ( k1_lattices(A_130,C_131,k6_lattices(A_130)) = k6_lattices(A_130)
      | ~ m1_subset_1(C_131,u1_struct_0(A_130))
      | ~ m1_subset_1(k6_lattices(A_130),u1_struct_0(A_130))
      | ~ v14_lattices(A_130)
      | ~ l2_lattices(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_430,plain,
    ( k1_lattices('#skF_7','#skF_8',k6_lattices('#skF_7')) = k6_lattices('#skF_7')
    | ~ m1_subset_1(k6_lattices('#skF_7'),u1_struct_0('#skF_7'))
    | ~ v14_lattices('#skF_7')
    | ~ l2_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_410])).

tff(c_445,plain,
    ( k1_lattices('#skF_7','#skF_8',k6_lattices('#skF_7')) = k6_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_74,c_266,c_430])).

tff(c_446,plain,(
    k1_lattices('#skF_7','#skF_8',k6_lattices('#skF_7')) = k6_lattices('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_445])).

tff(c_2984,plain,(
    ! [A_284,B_285,C_286] :
      ( r1_lattices(A_284,B_285,k1_lattices(A_284,B_285,C_286))
      | ~ m1_subset_1(C_286,u1_struct_0(A_284))
      | ~ m1_subset_1(B_285,u1_struct_0(A_284))
      | ~ l3_lattices(A_284)
      | ~ v9_lattices(A_284)
      | ~ v8_lattices(A_284)
      | ~ v6_lattices(A_284)
      | ~ v5_lattices(A_284)
      | v2_struct_0(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_3031,plain,
    ( r1_lattices('#skF_7','#skF_8',k6_lattices('#skF_7'))
    | ~ m1_subset_1(k6_lattices('#skF_7'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v9_lattices('#skF_7')
    | ~ v8_lattices('#skF_7')
    | ~ v6_lattices('#skF_7')
    | ~ v5_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_2984])).

tff(c_3060,plain,
    ( r1_lattices('#skF_7','#skF_8',k6_lattices('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_145,c_292,c_342,c_72,c_70,c_266,c_3031])).

tff(c_3061,plain,(
    r1_lattices('#skF_7','#skF_8',k6_lattices('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3060])).

tff(c_6,plain,(
    ! [A_1] :
      ( v7_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1729,plain,(
    ! [A_217,B_218,C_219] :
      ( r1_lattices(A_217,B_218,C_219)
      | k2_lattices(A_217,B_218,C_219) != B_218
      | ~ m1_subset_1(C_219,u1_struct_0(A_217))
      | ~ m1_subset_1(B_218,u1_struct_0(A_217))
      | ~ l3_lattices(A_217)
      | ~ v9_lattices(A_217)
      | ~ v8_lattices(A_217)
      | v2_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1749,plain,(
    ! [B_218] :
      ( r1_lattices('#skF_7',B_218,'#skF_8')
      | k2_lattices('#skF_7',B_218,'#skF_8') != B_218
      | ~ m1_subset_1(B_218,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v9_lattices('#skF_7')
      | ~ v8_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_1729])).

tff(c_1764,plain,(
    ! [B_218] :
      ( r1_lattices('#skF_7',B_218,'#skF_8')
      | k2_lattices('#skF_7',B_218,'#skF_8') != B_218
      | ~ m1_subset_1(B_218,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_342,c_72,c_1749])).

tff(c_1766,plain,(
    ! [B_220] :
      ( r1_lattices('#skF_7',B_220,'#skF_8')
      | k2_lattices('#skF_7',B_220,'#skF_8') != B_220
      | ~ m1_subset_1(B_220,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1764])).

tff(c_1838,plain,
    ( r1_lattices('#skF_7','#skF_8','#skF_8')
    | k2_lattices('#skF_7','#skF_8','#skF_8') != '#skF_8' ),
    inference(resolution,[status(thm)],[c_70,c_1766])).

tff(c_1839,plain,(
    k2_lattices('#skF_7','#skF_8','#skF_8') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1838])).

tff(c_315,plain,(
    ! [B_127] :
      ( r3_lattices('#skF_7',B_127,B_127)
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v9_lattices('#skF_7')
      | ~ v8_lattices('#skF_7')
      | ~ v6_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_295])).

tff(c_330,plain,(
    ! [B_127] :
      ( r3_lattices('#skF_7',B_127,B_127)
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_7'))
      | ~ v9_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_292,c_72,c_315])).

tff(c_331,plain,(
    ! [B_127] :
      ( r3_lattices('#skF_7',B_127,B_127)
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_7'))
      | ~ v9_lattices('#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_330])).

tff(c_345,plain,(
    ! [B_129] :
      ( r3_lattices('#skF_7',B_129,B_129)
      | ~ m1_subset_1(B_129,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_331])).

tff(c_407,plain,(
    r3_lattices('#skF_7','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_345])).

tff(c_2273,plain,(
    ! [A_247,B_248,C_249] :
      ( r1_lattices(A_247,B_248,C_249)
      | ~ r3_lattices(A_247,B_248,C_249)
      | ~ m1_subset_1(C_249,u1_struct_0(A_247))
      | ~ m1_subset_1(B_248,u1_struct_0(A_247))
      | ~ l3_lattices(A_247)
      | ~ v9_lattices(A_247)
      | ~ v8_lattices(A_247)
      | ~ v6_lattices(A_247)
      | v2_struct_0(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2293,plain,
    ( r1_lattices('#skF_7','#skF_8','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v9_lattices('#skF_7')
    | ~ v8_lattices('#skF_7')
    | ~ v6_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_407,c_2273])).

tff(c_2320,plain,
    ( r1_lattices('#skF_7','#skF_8','#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_292,c_342,c_72,c_70,c_2293])).

tff(c_2321,plain,(
    r1_lattices('#skF_7','#skF_8','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2320])).

tff(c_60,plain,(
    ! [A_63,B_67,C_69] :
      ( k2_lattices(A_63,B_67,C_69) = B_67
      | ~ r1_lattices(A_63,B_67,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(A_63))
      | ~ m1_subset_1(B_67,u1_struct_0(A_63))
      | ~ l3_lattices(A_63)
      | ~ v9_lattices(A_63)
      | ~ v8_lattices(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_2323,plain,
    ( k2_lattices('#skF_7','#skF_8','#skF_8') = '#skF_8'
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v9_lattices('#skF_7')
    | ~ v8_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2321,c_60])).

tff(c_2328,plain,
    ( k2_lattices('#skF_7','#skF_8','#skF_8') = '#skF_8'
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_342,c_72,c_70,c_2323])).

tff(c_2330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1839,c_2328])).

tff(c_2332,plain,(
    k2_lattices('#skF_7','#skF_8','#skF_8') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1838])).

tff(c_3511,plain,(
    ! [A_296,B_297,D_298,C_299] :
      ( r1_lattices(A_296,k2_lattices(A_296,B_297,D_298),k2_lattices(A_296,C_299,D_298))
      | ~ r1_lattices(A_296,B_297,C_299)
      | ~ m1_subset_1(D_298,u1_struct_0(A_296))
      | ~ m1_subset_1(C_299,u1_struct_0(A_296))
      | ~ m1_subset_1(B_297,u1_struct_0(A_296))
      | ~ l3_lattices(A_296)
      | ~ v9_lattices(A_296)
      | ~ v8_lattices(A_296)
      | ~ v7_lattices(A_296)
      | v2_struct_0(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_3548,plain,(
    ! [C_299] :
      ( r1_lattices('#skF_7','#skF_8',k2_lattices('#skF_7',C_299,'#skF_8'))
      | ~ r1_lattices('#skF_7','#skF_8',C_299)
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_299,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v9_lattices('#skF_7')
      | ~ v8_lattices('#skF_7')
      | ~ v7_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2332,c_3511])).

tff(c_3585,plain,(
    ! [C_299] :
      ( r1_lattices('#skF_7','#skF_8',k2_lattices('#skF_7',C_299,'#skF_8'))
      | ~ r1_lattices('#skF_7','#skF_8',C_299)
      | ~ m1_subset_1(C_299,u1_struct_0('#skF_7'))
      | ~ v7_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_342,c_72,c_70,c_70,c_3548])).

tff(c_3586,plain,(
    ! [C_299] :
      ( r1_lattices('#skF_7','#skF_8',k2_lattices('#skF_7',C_299,'#skF_8'))
      | ~ r1_lattices('#skF_7','#skF_8',C_299)
      | ~ m1_subset_1(C_299,u1_struct_0('#skF_7'))
      | ~ v7_lattices('#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3585])).

tff(c_3590,plain,(
    ~ v7_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3586])).

tff(c_3593,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_3590])).

tff(c_3596,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_3593])).

tff(c_3598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3596])).

tff(c_3626,plain,(
    ! [C_301] :
      ( r1_lattices('#skF_7','#skF_8',k2_lattices('#skF_7',C_301,'#skF_8'))
      | ~ r1_lattices('#skF_7','#skF_8',C_301)
      | ~ m1_subset_1(C_301,u1_struct_0('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_3586])).

tff(c_178,plain,
    ( k4_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8') = k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8')
    | ~ l2_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_146])).

tff(c_212,plain,
    ( k4_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8') = k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_178])).

tff(c_213,plain,(
    k4_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8') = k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_212])).

tff(c_68,plain,(
    k4_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_219,plain,(
    k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_68])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1731,plain,(
    ! [B_218] :
      ( r1_lattices('#skF_7',B_218,k6_lattices('#skF_7'))
      | k2_lattices('#skF_7',B_218,k6_lattices('#skF_7')) != B_218
      | ~ m1_subset_1(B_218,u1_struct_0('#skF_7'))
      | ~ l3_lattices('#skF_7')
      | ~ v9_lattices('#skF_7')
      | ~ v8_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_266,c_1729])).

tff(c_1752,plain,(
    ! [B_218] :
      ( r1_lattices('#skF_7',B_218,k6_lattices('#skF_7'))
      | k2_lattices('#skF_7',B_218,k6_lattices('#skF_7')) != B_218
      | ~ m1_subset_1(B_218,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_342,c_72,c_1731])).

tff(c_2384,plain,(
    ! [B_253] :
      ( r1_lattices('#skF_7',B_253,k6_lattices('#skF_7'))
      | k2_lattices('#skF_7',B_253,k6_lattices('#skF_7')) != B_253
      | ~ m1_subset_1(B_253,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1752])).

tff(c_64,plain,(
    ! [C_83,B_81,A_77] :
      ( C_83 = B_81
      | ~ r1_lattices(A_77,C_83,B_81)
      | ~ r1_lattices(A_77,B_81,C_83)
      | ~ m1_subset_1(C_83,u1_struct_0(A_77))
      | ~ m1_subset_1(B_81,u1_struct_0(A_77))
      | ~ l2_lattices(A_77)
      | ~ v4_lattices(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_2388,plain,(
    ! [B_253] :
      ( k6_lattices('#skF_7') = B_253
      | ~ r1_lattices('#skF_7',k6_lattices('#skF_7'),B_253)
      | ~ m1_subset_1(k6_lattices('#skF_7'),u1_struct_0('#skF_7'))
      | ~ l2_lattices('#skF_7')
      | ~ v4_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | k2_lattices('#skF_7',B_253,k6_lattices('#skF_7')) != B_253
      | ~ m1_subset_1(B_253,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_2384,c_64])).

tff(c_2395,plain,(
    ! [B_253] :
      ( k6_lattices('#skF_7') = B_253
      | ~ r1_lattices('#skF_7',k6_lattices('#skF_7'),B_253)
      | ~ v4_lattices('#skF_7')
      | v2_struct_0('#skF_7')
      | k2_lattices('#skF_7',B_253,k6_lattices('#skF_7')) != B_253
      | ~ m1_subset_1(B_253,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_266,c_2388])).

tff(c_2396,plain,(
    ! [B_253] :
      ( k6_lattices('#skF_7') = B_253
      | ~ r1_lattices('#skF_7',k6_lattices('#skF_7'),B_253)
      | ~ v4_lattices('#skF_7')
      | k2_lattices('#skF_7',B_253,k6_lattices('#skF_7')) != B_253
      | ~ m1_subset_1(B_253,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2395])).

tff(c_2397,plain,(
    ~ v4_lattices('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2396])).

tff(c_2400,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_2397])).

tff(c_2403,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_2400])).

tff(c_2405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2403])).

tff(c_2407,plain,(
    v4_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_2396])).

tff(c_42,plain,(
    ! [A_49,B_50,C_51] :
      ( m1_subset_1(k2_lattices(A_49,B_50,C_51),u1_struct_0(A_49))
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l1_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_568,plain,(
    ! [A_138,B_139,C_140] :
      ( k1_lattices(A_138,k2_lattices(A_138,B_139,C_140),C_140) = C_140
      | ~ m1_subset_1(C_140,u1_struct_0(A_138))
      | ~ m1_subset_1(B_139,u1_struct_0(A_138))
      | ~ v8_lattices(A_138)
      | ~ l3_lattices(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_588,plain,(
    ! [B_139] :
      ( k1_lattices('#skF_7',k2_lattices('#skF_7',B_139,'#skF_8'),'#skF_8') = '#skF_8'
      | ~ m1_subset_1(B_139,u1_struct_0('#skF_7'))
      | ~ v8_lattices('#skF_7')
      | ~ l3_lattices('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_70,c_568])).

tff(c_603,plain,(
    ! [B_139] :
      ( k1_lattices('#skF_7',k2_lattices('#skF_7',B_139,'#skF_8'),'#skF_8') = '#skF_8'
      | ~ m1_subset_1(B_139,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_292,c_588])).

tff(c_605,plain,(
    ! [B_141] :
      ( k1_lattices('#skF_7',k2_lattices('#skF_7',B_141,'#skF_8'),'#skF_8') = '#skF_8'
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_603])).

tff(c_644,plain,(
    k1_lattices('#skF_7',k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8'),'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_266,c_605])).

tff(c_3025,plain,
    ( r1_lattices('#skF_7',k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8'),'#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1(k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8'),u1_struct_0('#skF_7'))
    | ~ l3_lattices('#skF_7')
    | ~ v9_lattices('#skF_7')
    | ~ v8_lattices('#skF_7')
    | ~ v6_lattices('#skF_7')
    | ~ v5_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_2984])).

tff(c_3057,plain,
    ( r1_lattices('#skF_7',k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8'),'#skF_8')
    | ~ m1_subset_1(k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8'),u1_struct_0('#skF_7'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_145,c_292,c_342,c_72,c_70,c_3025])).

tff(c_3058,plain,
    ( r1_lattices('#skF_7',k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8'),'#skF_8')
    | ~ m1_subset_1(k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3057])).

tff(c_3125,plain,(
    ~ m1_subset_1(k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_3058])).

tff(c_3128,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ m1_subset_1(k6_lattices('#skF_7'),u1_struct_0('#skF_7'))
    | ~ l1_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_3125])).

tff(c_3131,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_266,c_70,c_3128])).

tff(c_3133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3131])).

tff(c_3135,plain,(
    m1_subset_1(k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8'),u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3058])).

tff(c_3134,plain,(
    r1_lattices('#skF_7',k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_3058])).

tff(c_3230,plain,
    ( k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8') = '#skF_8'
    | ~ r1_lattices('#skF_7','#skF_8',k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8'))
    | ~ m1_subset_1(k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8'),u1_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
    | ~ l2_lattices('#skF_7')
    | ~ v4_lattices('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_3134,c_64])).

tff(c_3237,plain,
    ( k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8') = '#skF_8'
    | ~ r1_lattices('#skF_7','#skF_8',k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8'))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2407,c_88,c_70,c_3135,c_3230])).

tff(c_3238,plain,(
    ~ r1_lattices('#skF_7','#skF_8',k2_lattices('#skF_7',k6_lattices('#skF_7'),'#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_219,c_3237])).

tff(c_3629,plain,
    ( ~ r1_lattices('#skF_7','#skF_8',k6_lattices('#skF_7'))
    | ~ m1_subset_1(k6_lattices('#skF_7'),u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_3626,c_3238])).

tff(c_3643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_3061,c_3629])).

tff(c_3645,plain,(
    ~ v8_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_3648,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_3645])).

tff(c_3651,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_3648])).

tff(c_3653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3651])).

tff(c_3655,plain,(
    ~ v5_lattices('#skF_7') ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_3658,plain,
    ( ~ v10_lattices('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l3_lattices('#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_3655])).

tff(c_3661,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_3658])).

tff(c_3663,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3661])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:43:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.69/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.69/2.13  
% 5.69/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.78/2.13  %$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v14_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k6_lattices > #skF_5 > #skF_2 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_6
% 5.78/2.13  
% 5.78/2.13  %Foreground sorts:
% 5.78/2.13  
% 5.78/2.13  
% 5.78/2.13  %Background operators:
% 5.78/2.13  
% 5.78/2.13  
% 5.78/2.13  %Foreground operators:
% 5.78/2.13  tff(l3_lattices, type, l3_lattices: $i > $o).
% 5.78/2.13  tff(k6_lattices, type, k6_lattices: $i > $i).
% 5.78/2.13  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.78/2.13  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 5.78/2.13  tff('#skF_5', type, '#skF_5': $i > $i).
% 5.78/2.13  tff(l2_lattices, type, l2_lattices: $i > $o).
% 5.78/2.13  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.78/2.13  tff('#skF_4', type, '#skF_4': $i > $i).
% 5.78/2.13  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 5.78/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.78/2.13  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 5.78/2.13  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 5.78/2.13  tff(l1_lattices, type, l1_lattices: $i > $o).
% 5.78/2.13  tff('#skF_7', type, '#skF_7': $i).
% 5.78/2.13  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 5.78/2.13  tff(v4_lattices, type, v4_lattices: $i > $o).
% 5.78/2.13  tff(v6_lattices, type, v6_lattices: $i > $o).
% 5.78/2.13  tff(v9_lattices, type, v9_lattices: $i > $o).
% 5.78/2.13  tff(v5_lattices, type, v5_lattices: $i > $o).
% 5.78/2.13  tff(v10_lattices, type, v10_lattices: $i > $o).
% 5.78/2.13  tff('#skF_8', type, '#skF_8': $i).
% 5.78/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.78/2.13  tff(v14_lattices, type, v14_lattices: $i > $o).
% 5.78/2.13  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.78/2.13  tff(v8_lattices, type, v8_lattices: $i > $o).
% 5.78/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.78/2.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.78/2.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.78/2.13  tff('#skF_6', type, '#skF_6': $i > $i).
% 5.78/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.78/2.13  tff(v7_lattices, type, v7_lattices: $i > $o).
% 5.78/2.13  
% 5.78/2.16  tff(f_270, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v14_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattices(A, k6_lattices(A), B) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_lattices)).
% 5.78/2.16  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 5.78/2.16  tff(f_123, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 5.78/2.16  tff(f_117, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => m1_subset_1(k6_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_lattices)).
% 5.78/2.16  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (v14_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k6_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k1_lattices(A, B, C) = B) & (k1_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattices)).
% 5.78/2.16  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (v5_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (k1_lattices(A, B, k1_lattices(A, C, D)) = k1_lattices(A, k1_lattices(A, B, C), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_lattices)).
% 5.78/2.16  tff(f_136, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 5.78/2.16  tff(f_99, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 5.78/2.16  tff(f_172, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_lattices(A, B, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_lattices)).
% 5.78/2.16  tff(f_212, axiom, (![A]: ((((((~v2_struct_0(A) & v5_lattices(A)) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r1_lattices(A, B, k1_lattices(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_lattices)).
% 5.78/2.16  tff(f_191, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 5.78/2.16  tff(f_155, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 5.78/2.16  tff(f_255, axiom, (![A]: (((((~v2_struct_0(A) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattices(A, B, C) => r1_lattices(A, k2_lattices(A, B, D), k2_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_lattices)).
% 5.78/2.16  tff(f_231, axiom, (![A]: (((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_lattices(A, B, C) & r1_lattices(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_lattices)).
% 5.78/2.16  tff(f_110, axiom, (![A, B, C]: ((((~v2_struct_0(A) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k2_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_lattices)).
% 5.78/2.16  tff(c_78, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_270])).
% 5.78/2.16  tff(c_72, plain, (l3_lattices('#skF_7')), inference(cnfTransformation, [status(thm)], [f_270])).
% 5.78/2.16  tff(c_76, plain, (v10_lattices('#skF_7')), inference(cnfTransformation, [status(thm)], [f_270])).
% 5.78/2.16  tff(c_10, plain, (![A_1]: (v5_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.78/2.16  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.78/2.16  tff(c_84, plain, (![A_101]: (l2_lattices(A_101) | ~l3_lattices(A_101))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.78/2.16  tff(c_88, plain, (l2_lattices('#skF_7')), inference(resolution, [status(thm)], [c_72, c_84])).
% 5.78/2.16  tff(c_44, plain, (![A_52]: (m1_subset_1(k6_lattices(A_52), u1_struct_0(A_52)) | ~l2_lattices(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.78/2.16  tff(c_74, plain, (v14_lattices('#skF_7')), inference(cnfTransformation, [status(thm)], [f_270])).
% 5.78/2.16  tff(c_70, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_270])).
% 5.78/2.16  tff(c_225, plain, (![A_124, C_125]: (k1_lattices(A_124, k6_lattices(A_124), C_125)=k6_lattices(A_124) | ~m1_subset_1(C_125, u1_struct_0(A_124)) | ~m1_subset_1(k6_lattices(A_124), u1_struct_0(A_124)) | ~v14_lattices(A_124) | ~l2_lattices(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.78/2.16  tff(c_243, plain, (k1_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8')=k6_lattices('#skF_7') | ~m1_subset_1(k6_lattices('#skF_7'), u1_struct_0('#skF_7')) | ~v14_lattices('#skF_7') | ~l2_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_70, c_225])).
% 5.78/2.16  tff(c_254, plain, (k1_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8')=k6_lattices('#skF_7') | ~m1_subset_1(k6_lattices('#skF_7'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_74, c_243])).
% 5.78/2.16  tff(c_255, plain, (k1_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8')=k6_lattices('#skF_7') | ~m1_subset_1(k6_lattices('#skF_7'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_254])).
% 5.78/2.16  tff(c_256, plain, (~m1_subset_1(k6_lattices('#skF_7'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_255])).
% 5.78/2.16  tff(c_259, plain, (~l2_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_44, c_256])).
% 5.78/2.16  tff(c_262, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_259])).
% 5.78/2.16  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_262])).
% 5.78/2.16  tff(c_266, plain, (m1_subset_1(k6_lattices('#skF_7'), u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_255])).
% 5.78/2.16  tff(c_28, plain, (![A_12]: (m1_subset_1('#skF_4'(A_12), u1_struct_0(A_12)) | v5_lattices(A_12) | ~l2_lattices(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.78/2.16  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.78/2.16  tff(c_79, plain, (![A_100]: (l1_lattices(A_100) | ~l3_lattices(A_100))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.78/2.16  tff(c_83, plain, (l1_lattices('#skF_7')), inference(resolution, [status(thm)], [c_72, c_79])).
% 5.78/2.16  tff(c_104, plain, (![A_120, B_121, C_122]: (k4_lattices(A_120, B_121, C_122)=k2_lattices(A_120, B_121, C_122) | ~m1_subset_1(C_122, u1_struct_0(A_120)) | ~m1_subset_1(B_121, u1_struct_0(A_120)) | ~l1_lattices(A_120) | ~v6_lattices(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.78/2.16  tff(c_122, plain, (![B_121]: (k4_lattices('#skF_7', B_121, '#skF_8')=k2_lattices('#skF_7', B_121, '#skF_8') | ~m1_subset_1(B_121, u1_struct_0('#skF_7')) | ~l1_lattices('#skF_7') | ~v6_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_104])).
% 5.78/2.16  tff(c_133, plain, (![B_121]: (k4_lattices('#skF_7', B_121, '#skF_8')=k2_lattices('#skF_7', B_121, '#skF_8') | ~m1_subset_1(B_121, u1_struct_0('#skF_7')) | ~v6_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_122])).
% 5.78/2.16  tff(c_134, plain, (![B_121]: (k4_lattices('#skF_7', B_121, '#skF_8')=k2_lattices('#skF_7', B_121, '#skF_8') | ~m1_subset_1(B_121, u1_struct_0('#skF_7')) | ~v6_lattices('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_133])).
% 5.78/2.16  tff(c_135, plain, (~v6_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_134])).
% 5.78/2.16  tff(c_138, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_8, c_135])).
% 5.78/2.16  tff(c_141, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_138])).
% 5.78/2.16  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_141])).
% 5.78/2.16  tff(c_146, plain, (![B_123]: (k4_lattices('#skF_7', B_123, '#skF_8')=k2_lattices('#skF_7', B_123, '#skF_8') | ~m1_subset_1(B_123, u1_struct_0('#skF_7')))), inference(splitRight, [status(thm)], [c_134])).
% 5.78/2.16  tff(c_162, plain, (k4_lattices('#skF_7', '#skF_4'('#skF_7'), '#skF_8')=k2_lattices('#skF_7', '#skF_4'('#skF_7'), '#skF_8') | v5_lattices('#skF_7') | ~l2_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_28, c_146])).
% 5.78/2.16  tff(c_196, plain, (k4_lattices('#skF_7', '#skF_4'('#skF_7'), '#skF_8')=k2_lattices('#skF_7', '#skF_4'('#skF_7'), '#skF_8') | v5_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_162])).
% 5.78/2.16  tff(c_197, plain, (k4_lattices('#skF_7', '#skF_4'('#skF_7'), '#skF_8')=k2_lattices('#skF_7', '#skF_4'('#skF_7'), '#skF_8') | v5_lattices('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_78, c_196])).
% 5.78/2.16  tff(c_224, plain, (v5_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_197])).
% 5.78/2.16  tff(c_145, plain, (v6_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_134])).
% 5.78/2.16  tff(c_38, plain, (![A_38]: (m1_subset_1('#skF_6'(A_38), u1_struct_0(A_38)) | v8_lattices(A_38) | ~l3_lattices(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.78/2.16  tff(c_166, plain, (k4_lattices('#skF_7', '#skF_6'('#skF_7'), '#skF_8')=k2_lattices('#skF_7', '#skF_6'('#skF_7'), '#skF_8') | v8_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_38, c_146])).
% 5.78/2.16  tff(c_200, plain, (k4_lattices('#skF_7', '#skF_6'('#skF_7'), '#skF_8')=k2_lattices('#skF_7', '#skF_6'('#skF_7'), '#skF_8') | v8_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_166])).
% 5.78/2.16  tff(c_201, plain, (k4_lattices('#skF_7', '#skF_6'('#skF_7'), '#skF_8')=k2_lattices('#skF_7', '#skF_6'('#skF_7'), '#skF_8') | v8_lattices('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_78, c_200])).
% 5.78/2.16  tff(c_292, plain, (v8_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_201])).
% 5.78/2.16  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.78/2.16  tff(c_295, plain, (![A_126, B_127, C_128]: (r3_lattices(A_126, B_127, B_127) | ~m1_subset_1(C_128, u1_struct_0(A_126)) | ~m1_subset_1(B_127, u1_struct_0(A_126)) | ~l3_lattices(A_126) | ~v9_lattices(A_126) | ~v8_lattices(A_126) | ~v6_lattices(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.78/2.16  tff(c_297, plain, (![B_127]: (r3_lattices('#skF_7', B_127, B_127) | ~m1_subset_1(B_127, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | ~v6_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_266, c_295])).
% 5.78/2.16  tff(c_318, plain, (![B_127]: (r3_lattices('#skF_7', B_127, B_127) | ~m1_subset_1(B_127, u1_struct_0('#skF_7')) | ~v9_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_292, c_72, c_297])).
% 5.78/2.16  tff(c_319, plain, (![B_127]: (r3_lattices('#skF_7', B_127, B_127) | ~m1_subset_1(B_127, u1_struct_0('#skF_7')) | ~v9_lattices('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_318])).
% 5.78/2.16  tff(c_332, plain, (~v9_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_319])).
% 5.78/2.16  tff(c_335, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_2, c_332])).
% 5.78/2.16  tff(c_338, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_335])).
% 5.78/2.16  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_338])).
% 5.78/2.16  tff(c_342, plain, (v9_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_319])).
% 5.78/2.16  tff(c_410, plain, (![A_130, C_131]: (k1_lattices(A_130, C_131, k6_lattices(A_130))=k6_lattices(A_130) | ~m1_subset_1(C_131, u1_struct_0(A_130)) | ~m1_subset_1(k6_lattices(A_130), u1_struct_0(A_130)) | ~v14_lattices(A_130) | ~l2_lattices(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.78/2.16  tff(c_430, plain, (k1_lattices('#skF_7', '#skF_8', k6_lattices('#skF_7'))=k6_lattices('#skF_7') | ~m1_subset_1(k6_lattices('#skF_7'), u1_struct_0('#skF_7')) | ~v14_lattices('#skF_7') | ~l2_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_70, c_410])).
% 5.78/2.16  tff(c_445, plain, (k1_lattices('#skF_7', '#skF_8', k6_lattices('#skF_7'))=k6_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_74, c_266, c_430])).
% 5.78/2.16  tff(c_446, plain, (k1_lattices('#skF_7', '#skF_8', k6_lattices('#skF_7'))=k6_lattices('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_78, c_445])).
% 5.78/2.16  tff(c_2984, plain, (![A_284, B_285, C_286]: (r1_lattices(A_284, B_285, k1_lattices(A_284, B_285, C_286)) | ~m1_subset_1(C_286, u1_struct_0(A_284)) | ~m1_subset_1(B_285, u1_struct_0(A_284)) | ~l3_lattices(A_284) | ~v9_lattices(A_284) | ~v8_lattices(A_284) | ~v6_lattices(A_284) | ~v5_lattices(A_284) | v2_struct_0(A_284))), inference(cnfTransformation, [status(thm)], [f_212])).
% 5.78/2.16  tff(c_3031, plain, (r1_lattices('#skF_7', '#skF_8', k6_lattices('#skF_7')) | ~m1_subset_1(k6_lattices('#skF_7'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | ~v6_lattices('#skF_7') | ~v5_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_446, c_2984])).
% 5.78/2.16  tff(c_3060, plain, (r1_lattices('#skF_7', '#skF_8', k6_lattices('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_145, c_292, c_342, c_72, c_70, c_266, c_3031])).
% 5.78/2.16  tff(c_3061, plain, (r1_lattices('#skF_7', '#skF_8', k6_lattices('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_3060])).
% 5.78/2.16  tff(c_6, plain, (![A_1]: (v7_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.78/2.16  tff(c_1729, plain, (![A_217, B_218, C_219]: (r1_lattices(A_217, B_218, C_219) | k2_lattices(A_217, B_218, C_219)!=B_218 | ~m1_subset_1(C_219, u1_struct_0(A_217)) | ~m1_subset_1(B_218, u1_struct_0(A_217)) | ~l3_lattices(A_217) | ~v9_lattices(A_217) | ~v8_lattices(A_217) | v2_struct_0(A_217))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.78/2.16  tff(c_1749, plain, (![B_218]: (r1_lattices('#skF_7', B_218, '#skF_8') | k2_lattices('#skF_7', B_218, '#skF_8')!=B_218 | ~m1_subset_1(B_218, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_1729])).
% 5.78/2.16  tff(c_1764, plain, (![B_218]: (r1_lattices('#skF_7', B_218, '#skF_8') | k2_lattices('#skF_7', B_218, '#skF_8')!=B_218 | ~m1_subset_1(B_218, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_342, c_72, c_1749])).
% 5.78/2.16  tff(c_1766, plain, (![B_220]: (r1_lattices('#skF_7', B_220, '#skF_8') | k2_lattices('#skF_7', B_220, '#skF_8')!=B_220 | ~m1_subset_1(B_220, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_78, c_1764])).
% 5.78/2.16  tff(c_1838, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_8') | k2_lattices('#skF_7', '#skF_8', '#skF_8')!='#skF_8'), inference(resolution, [status(thm)], [c_70, c_1766])).
% 5.78/2.16  tff(c_1839, plain, (k2_lattices('#skF_7', '#skF_8', '#skF_8')!='#skF_8'), inference(splitLeft, [status(thm)], [c_1838])).
% 5.78/2.16  tff(c_315, plain, (![B_127]: (r3_lattices('#skF_7', B_127, B_127) | ~m1_subset_1(B_127, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | ~v6_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_295])).
% 5.78/2.16  tff(c_330, plain, (![B_127]: (r3_lattices('#skF_7', B_127, B_127) | ~m1_subset_1(B_127, u1_struct_0('#skF_7')) | ~v9_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_292, c_72, c_315])).
% 5.78/2.16  tff(c_331, plain, (![B_127]: (r3_lattices('#skF_7', B_127, B_127) | ~m1_subset_1(B_127, u1_struct_0('#skF_7')) | ~v9_lattices('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_330])).
% 5.78/2.16  tff(c_345, plain, (![B_129]: (r3_lattices('#skF_7', B_129, B_129) | ~m1_subset_1(B_129, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_331])).
% 5.78/2.16  tff(c_407, plain, (r3_lattices('#skF_7', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_70, c_345])).
% 5.78/2.16  tff(c_2273, plain, (![A_247, B_248, C_249]: (r1_lattices(A_247, B_248, C_249) | ~r3_lattices(A_247, B_248, C_249) | ~m1_subset_1(C_249, u1_struct_0(A_247)) | ~m1_subset_1(B_248, u1_struct_0(A_247)) | ~l3_lattices(A_247) | ~v9_lattices(A_247) | ~v8_lattices(A_247) | ~v6_lattices(A_247) | v2_struct_0(A_247))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.78/2.16  tff(c_2293, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | ~v6_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_407, c_2273])).
% 5.78/2.16  tff(c_2320, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_292, c_342, c_72, c_70, c_2293])).
% 5.78/2.16  tff(c_2321, plain, (r1_lattices('#skF_7', '#skF_8', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_78, c_2320])).
% 5.78/2.16  tff(c_60, plain, (![A_63, B_67, C_69]: (k2_lattices(A_63, B_67, C_69)=B_67 | ~r1_lattices(A_63, B_67, C_69) | ~m1_subset_1(C_69, u1_struct_0(A_63)) | ~m1_subset_1(B_67, u1_struct_0(A_63)) | ~l3_lattices(A_63) | ~v9_lattices(A_63) | ~v8_lattices(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.78/2.16  tff(c_2323, plain, (k2_lattices('#skF_7', '#skF_8', '#skF_8')='#skF_8' | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_2321, c_60])).
% 5.78/2.16  tff(c_2328, plain, (k2_lattices('#skF_7', '#skF_8', '#skF_8')='#skF_8' | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_292, c_342, c_72, c_70, c_2323])).
% 5.78/2.16  tff(c_2330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1839, c_2328])).
% 5.78/2.16  tff(c_2332, plain, (k2_lattices('#skF_7', '#skF_8', '#skF_8')='#skF_8'), inference(splitRight, [status(thm)], [c_1838])).
% 5.78/2.16  tff(c_3511, plain, (![A_296, B_297, D_298, C_299]: (r1_lattices(A_296, k2_lattices(A_296, B_297, D_298), k2_lattices(A_296, C_299, D_298)) | ~r1_lattices(A_296, B_297, C_299) | ~m1_subset_1(D_298, u1_struct_0(A_296)) | ~m1_subset_1(C_299, u1_struct_0(A_296)) | ~m1_subset_1(B_297, u1_struct_0(A_296)) | ~l3_lattices(A_296) | ~v9_lattices(A_296) | ~v8_lattices(A_296) | ~v7_lattices(A_296) | v2_struct_0(A_296))), inference(cnfTransformation, [status(thm)], [f_255])).
% 5.78/2.16  tff(c_3548, plain, (![C_299]: (r1_lattices('#skF_7', '#skF_8', k2_lattices('#skF_7', C_299, '#skF_8')) | ~r1_lattices('#skF_7', '#skF_8', C_299) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1(C_299, u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | ~v7_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2332, c_3511])).
% 5.78/2.16  tff(c_3585, plain, (![C_299]: (r1_lattices('#skF_7', '#skF_8', k2_lattices('#skF_7', C_299, '#skF_8')) | ~r1_lattices('#skF_7', '#skF_8', C_299) | ~m1_subset_1(C_299, u1_struct_0('#skF_7')) | ~v7_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_342, c_72, c_70, c_70, c_3548])).
% 5.78/2.16  tff(c_3586, plain, (![C_299]: (r1_lattices('#skF_7', '#skF_8', k2_lattices('#skF_7', C_299, '#skF_8')) | ~r1_lattices('#skF_7', '#skF_8', C_299) | ~m1_subset_1(C_299, u1_struct_0('#skF_7')) | ~v7_lattices('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_3585])).
% 5.78/2.16  tff(c_3590, plain, (~v7_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_3586])).
% 5.78/2.16  tff(c_3593, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_6, c_3590])).
% 5.78/2.16  tff(c_3596, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_3593])).
% 5.78/2.16  tff(c_3598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_3596])).
% 5.78/2.16  tff(c_3626, plain, (![C_301]: (r1_lattices('#skF_7', '#skF_8', k2_lattices('#skF_7', C_301, '#skF_8')) | ~r1_lattices('#skF_7', '#skF_8', C_301) | ~m1_subset_1(C_301, u1_struct_0('#skF_7')))), inference(splitRight, [status(thm)], [c_3586])).
% 5.78/2.16  tff(c_178, plain, (k4_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8')=k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8') | ~l2_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_44, c_146])).
% 5.78/2.16  tff(c_212, plain, (k4_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8')=k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_178])).
% 5.78/2.16  tff(c_213, plain, (k4_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8')=k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_78, c_212])).
% 5.78/2.16  tff(c_68, plain, (k4_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_270])).
% 5.78/2.16  tff(c_219, plain, (k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_213, c_68])).
% 5.78/2.16  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.78/2.16  tff(c_1731, plain, (![B_218]: (r1_lattices('#skF_7', B_218, k6_lattices('#skF_7')) | k2_lattices('#skF_7', B_218, k6_lattices('#skF_7'))!=B_218 | ~m1_subset_1(B_218, u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_266, c_1729])).
% 5.78/2.16  tff(c_1752, plain, (![B_218]: (r1_lattices('#skF_7', B_218, k6_lattices('#skF_7')) | k2_lattices('#skF_7', B_218, k6_lattices('#skF_7'))!=B_218 | ~m1_subset_1(B_218, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_342, c_72, c_1731])).
% 5.78/2.16  tff(c_2384, plain, (![B_253]: (r1_lattices('#skF_7', B_253, k6_lattices('#skF_7')) | k2_lattices('#skF_7', B_253, k6_lattices('#skF_7'))!=B_253 | ~m1_subset_1(B_253, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_78, c_1752])).
% 5.78/2.16  tff(c_64, plain, (![C_83, B_81, A_77]: (C_83=B_81 | ~r1_lattices(A_77, C_83, B_81) | ~r1_lattices(A_77, B_81, C_83) | ~m1_subset_1(C_83, u1_struct_0(A_77)) | ~m1_subset_1(B_81, u1_struct_0(A_77)) | ~l2_lattices(A_77) | ~v4_lattices(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_231])).
% 5.78/2.16  tff(c_2388, plain, (![B_253]: (k6_lattices('#skF_7')=B_253 | ~r1_lattices('#skF_7', k6_lattices('#skF_7'), B_253) | ~m1_subset_1(k6_lattices('#skF_7'), u1_struct_0('#skF_7')) | ~l2_lattices('#skF_7') | ~v4_lattices('#skF_7') | v2_struct_0('#skF_7') | k2_lattices('#skF_7', B_253, k6_lattices('#skF_7'))!=B_253 | ~m1_subset_1(B_253, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_2384, c_64])).
% 5.78/2.16  tff(c_2395, plain, (![B_253]: (k6_lattices('#skF_7')=B_253 | ~r1_lattices('#skF_7', k6_lattices('#skF_7'), B_253) | ~v4_lattices('#skF_7') | v2_struct_0('#skF_7') | k2_lattices('#skF_7', B_253, k6_lattices('#skF_7'))!=B_253 | ~m1_subset_1(B_253, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_266, c_2388])).
% 5.78/2.16  tff(c_2396, plain, (![B_253]: (k6_lattices('#skF_7')=B_253 | ~r1_lattices('#skF_7', k6_lattices('#skF_7'), B_253) | ~v4_lattices('#skF_7') | k2_lattices('#skF_7', B_253, k6_lattices('#skF_7'))!=B_253 | ~m1_subset_1(B_253, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_78, c_2395])).
% 5.78/2.16  tff(c_2397, plain, (~v4_lattices('#skF_7')), inference(splitLeft, [status(thm)], [c_2396])).
% 5.78/2.16  tff(c_2400, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_12, c_2397])).
% 5.78/2.16  tff(c_2403, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_2400])).
% 5.78/2.16  tff(c_2405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_2403])).
% 5.78/2.16  tff(c_2407, plain, (v4_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_2396])).
% 5.78/2.16  tff(c_42, plain, (![A_49, B_50, C_51]: (m1_subset_1(k2_lattices(A_49, B_50, C_51), u1_struct_0(A_49)) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l1_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.78/2.16  tff(c_568, plain, (![A_138, B_139, C_140]: (k1_lattices(A_138, k2_lattices(A_138, B_139, C_140), C_140)=C_140 | ~m1_subset_1(C_140, u1_struct_0(A_138)) | ~m1_subset_1(B_139, u1_struct_0(A_138)) | ~v8_lattices(A_138) | ~l3_lattices(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.78/2.16  tff(c_588, plain, (![B_139]: (k1_lattices('#skF_7', k2_lattices('#skF_7', B_139, '#skF_8'), '#skF_8')='#skF_8' | ~m1_subset_1(B_139, u1_struct_0('#skF_7')) | ~v8_lattices('#skF_7') | ~l3_lattices('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_568])).
% 5.78/2.16  tff(c_603, plain, (![B_139]: (k1_lattices('#skF_7', k2_lattices('#skF_7', B_139, '#skF_8'), '#skF_8')='#skF_8' | ~m1_subset_1(B_139, u1_struct_0('#skF_7')) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_292, c_588])).
% 5.78/2.16  tff(c_605, plain, (![B_141]: (k1_lattices('#skF_7', k2_lattices('#skF_7', B_141, '#skF_8'), '#skF_8')='#skF_8' | ~m1_subset_1(B_141, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_78, c_603])).
% 5.78/2.16  tff(c_644, plain, (k1_lattices('#skF_7', k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8'), '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_266, c_605])).
% 5.78/2.16  tff(c_3025, plain, (r1_lattices('#skF_7', k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8'), '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1(k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8'), u1_struct_0('#skF_7')) | ~l3_lattices('#skF_7') | ~v9_lattices('#skF_7') | ~v8_lattices('#skF_7') | ~v6_lattices('#skF_7') | ~v5_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_644, c_2984])).
% 5.78/2.16  tff(c_3057, plain, (r1_lattices('#skF_7', k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8'), '#skF_8') | ~m1_subset_1(k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8'), u1_struct_0('#skF_7')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_145, c_292, c_342, c_72, c_70, c_3025])).
% 5.78/2.16  tff(c_3058, plain, (r1_lattices('#skF_7', k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8'), '#skF_8') | ~m1_subset_1(k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_3057])).
% 5.78/2.16  tff(c_3125, plain, (~m1_subset_1(k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8'), u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_3058])).
% 5.78/2.16  tff(c_3128, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~m1_subset_1(k6_lattices('#skF_7'), u1_struct_0('#skF_7')) | ~l1_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_42, c_3125])).
% 5.78/2.16  tff(c_3131, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_266, c_70, c_3128])).
% 5.78/2.16  tff(c_3133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_3131])).
% 5.78/2.16  tff(c_3135, plain, (m1_subset_1(k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8'), u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_3058])).
% 5.78/2.16  tff(c_3134, plain, (r1_lattices('#skF_7', k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_3058])).
% 5.78/2.16  tff(c_3230, plain, (k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8')='#skF_8' | ~r1_lattices('#skF_7', '#skF_8', k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8')) | ~m1_subset_1(k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8'), u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | ~l2_lattices('#skF_7') | ~v4_lattices('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_3134, c_64])).
% 5.78/2.16  tff(c_3237, plain, (k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8')='#skF_8' | ~r1_lattices('#skF_7', '#skF_8', k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8')) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2407, c_88, c_70, c_3135, c_3230])).
% 5.78/2.16  tff(c_3238, plain, (~r1_lattices('#skF_7', '#skF_8', k2_lattices('#skF_7', k6_lattices('#skF_7'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_78, c_219, c_3237])).
% 5.78/2.16  tff(c_3629, plain, (~r1_lattices('#skF_7', '#skF_8', k6_lattices('#skF_7')) | ~m1_subset_1(k6_lattices('#skF_7'), u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_3626, c_3238])).
% 5.78/2.16  tff(c_3643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_266, c_3061, c_3629])).
% 5.78/2.16  tff(c_3645, plain, (~v8_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_201])).
% 5.78/2.16  tff(c_3648, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_4, c_3645])).
% 5.78/2.16  tff(c_3651, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_3648])).
% 5.78/2.16  tff(c_3653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_3651])).
% 5.78/2.16  tff(c_3655, plain, (~v5_lattices('#skF_7')), inference(splitRight, [status(thm)], [c_197])).
% 5.78/2.16  tff(c_3658, plain, (~v10_lattices('#skF_7') | v2_struct_0('#skF_7') | ~l3_lattices('#skF_7')), inference(resolution, [status(thm)], [c_10, c_3655])).
% 5.78/2.16  tff(c_3661, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_3658])).
% 5.78/2.16  tff(c_3663, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_3661])).
% 5.78/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.78/2.16  
% 5.78/2.16  Inference rules
% 5.78/2.16  ----------------------
% 5.78/2.16  #Ref     : 0
% 5.78/2.16  #Sup     : 683
% 5.78/2.16  #Fact    : 0
% 5.78/2.16  #Define  : 0
% 5.78/2.16  #Split   : 15
% 5.78/2.16  #Chain   : 0
% 5.78/2.16  #Close   : 0
% 5.78/2.16  
% 5.78/2.16  Ordering : KBO
% 5.78/2.16  
% 5.78/2.16  Simplification rules
% 5.78/2.16  ----------------------
% 5.78/2.16  #Subsume      : 42
% 5.78/2.16  #Demod        : 1136
% 5.78/2.16  #Tautology    : 384
% 5.78/2.16  #SimpNegUnit  : 301
% 5.78/2.16  #BackRed      : 22
% 5.78/2.16  
% 5.78/2.16  #Partial instantiations: 0
% 5.78/2.16  #Strategies tried      : 1
% 5.78/2.16  
% 5.78/2.16  Timing (in seconds)
% 5.78/2.16  ----------------------
% 5.78/2.16  Preprocessing        : 0.41
% 5.78/2.16  Parsing              : 0.22
% 5.78/2.16  CNF conversion       : 0.03
% 5.78/2.16  Main loop            : 0.90
% 5.78/2.16  Inferencing          : 0.32
% 5.78/2.16  Reduction            : 0.30
% 5.78/2.16  Demodulation         : 0.21
% 5.78/2.16  BG Simplification    : 0.05
% 5.78/2.16  Subsumption          : 0.18
% 5.78/2.16  Abstraction          : 0.06
% 5.78/2.16  MUC search           : 0.00
% 5.78/2.16  Cooper               : 0.00
% 5.78/2.16  Total                : 1.37
% 5.78/2.16  Index Insertion      : 0.00
% 5.78/2.16  Index Deletion       : 0.00
% 5.78/2.16  Index Matching       : 0.00
% 5.78/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
