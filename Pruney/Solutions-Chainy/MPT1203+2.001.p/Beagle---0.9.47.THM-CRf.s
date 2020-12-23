%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:13 EST 2020

% Result     : Theorem 8.51s
% Output     : CNFRefutation 8.85s
% Verified   : 
% Statistics : Number of formulae       :  226 (1956 expanded)
%              Number of leaves         :   46 ( 672 expanded)
%              Depth                    :   21
%              Number of atoms          :  554 (8906 expanded)
%              Number of equality atoms :  152 (2129 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v11_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_7 > #skF_5 > #skF_2 > #skF_4 > #skF_11 > #skF_1 > #skF_8 > #skF_10 > #skF_9 > #skF_3 > #skF_6 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k3_lattices,type,(
    k3_lattices: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

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

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v11_lattices,type,(
    v11_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_244,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v11_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( k4_lattices(A,B,C) = k4_lattices(A,B,D)
                        & k3_lattices(A,B,C) = k3_lattices(A,B,D) )
                     => C = D ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_lattices)).

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

tff(f_200,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k1_lattices(A,B,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).

tff(f_158,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

tff(f_219,axiom,(
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

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v11_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => k2_lattices(A,B,k1_lattices(A,C,D)) = k1_lattices(A,k2_lattices(A,B,C),k2_lattices(A,B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattices)).

tff(f_171,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k3_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

tff(f_184,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k4_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

tff(f_139,axiom,(
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

tff(c_86,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_68,plain,(
    '#skF_11' != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_80,plain,(
    l3_lattices('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_82,plain,(
    v11_lattices('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_74,plain,(
    m1_subset_1('#skF_12',u1_struct_0('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_76,plain,(
    m1_subset_1('#skF_11',u1_struct_0('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_78,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_84,plain,(
    v10_lattices('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_120,plain,(
    ! [A_126,B_127] :
      ( k1_lattices(A_126,B_127,B_127) = B_127
      | ~ m1_subset_1(B_127,u1_struct_0(A_126))
      | ~ l3_lattices(A_126)
      | ~ v9_lattices(A_126)
      | ~ v8_lattices(A_126)
      | ~ v6_lattices(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_138,plain,
    ( k1_lattices('#skF_9','#skF_10','#skF_10') = '#skF_10'
    | ~ l3_lattices('#skF_9')
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | ~ v6_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_120])).

tff(c_153,plain,
    ( k1_lattices('#skF_9','#skF_10','#skF_10') = '#skF_10'
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | ~ v6_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_138])).

tff(c_154,plain,
    ( k1_lattices('#skF_9','#skF_10','#skF_10') = '#skF_10'
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | ~ v6_lattices('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_153])).

tff(c_163,plain,(
    ~ v6_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_166,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_8,c_163])).

tff(c_169,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_84,c_166])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_169])).

tff(c_172,plain,
    ( ~ v8_lattices('#skF_9')
    | ~ v9_lattices('#skF_9')
    | k1_lattices('#skF_9','#skF_10','#skF_10') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_174,plain,(
    ~ v9_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_177,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_2,c_174])).

tff(c_180,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_84,c_177])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_180])).

tff(c_183,plain,
    ( ~ v8_lattices('#skF_9')
    | k1_lattices('#skF_9','#skF_10','#skF_10') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_186,plain,(
    ~ v8_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_189,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_4,c_186])).

tff(c_192,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_84,c_189])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_192])).

tff(c_196,plain,(
    v8_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_184,plain,(
    v9_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_173,plain,(
    v6_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_142,plain,
    ( k1_lattices('#skF_9','#skF_12','#skF_12') = '#skF_12'
    | ~ l3_lattices('#skF_9')
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | ~ v6_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_120])).

tff(c_161,plain,
    ( k1_lattices('#skF_9','#skF_12','#skF_12') = '#skF_12'
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | ~ v6_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_142])).

tff(c_162,plain,
    ( k1_lattices('#skF_9','#skF_12','#skF_12') = '#skF_12'
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | ~ v6_lattices('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_161])).

tff(c_198,plain,
    ( k1_lattices('#skF_9','#skF_12','#skF_12') = '#skF_12'
    | ~ v8_lattices('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_184,c_162])).

tff(c_199,plain,(
    ~ v8_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_199])).

tff(c_202,plain,(
    k1_lattices('#skF_9','#skF_12','#skF_12') = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_92,plain,(
    ! [A_110] :
      ( l2_lattices(A_110)
      | ~ l3_lattices(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_96,plain,(
    l2_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_92])).

tff(c_209,plain,(
    ! [A_131,B_132,C_133] :
      ( r1_lattices(A_131,B_132,C_133)
      | k1_lattices(A_131,B_132,C_133) != C_133
      | ~ m1_subset_1(C_133,u1_struct_0(A_131))
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ l2_lattices(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_231,plain,(
    ! [B_132] :
      ( r1_lattices('#skF_9',B_132,'#skF_12')
      | k1_lattices('#skF_9',B_132,'#skF_12') != '#skF_12'
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_9'))
      | ~ l2_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_74,c_209])).

tff(c_250,plain,(
    ! [B_132] :
      ( r1_lattices('#skF_9',B_132,'#skF_12')
      | k1_lattices('#skF_9',B_132,'#skF_12') != '#skF_12'
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_231])).

tff(c_349,plain,(
    ! [B_135] :
      ( r1_lattices('#skF_9',B_135,'#skF_12')
      | k1_lattices('#skF_9',B_135,'#skF_12') != '#skF_12'
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_250])).

tff(c_390,plain,
    ( r1_lattices('#skF_9','#skF_12','#skF_12')
    | k1_lattices('#skF_9','#skF_12','#skF_12') != '#skF_12' ),
    inference(resolution,[status(thm)],[c_74,c_349])).

tff(c_427,plain,(
    r1_lattices('#skF_9','#skF_12','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_390])).

tff(c_1802,plain,(
    ! [A_160,B_161,C_162] :
      ( k2_lattices(A_160,B_161,C_162) = B_161
      | ~ r1_lattices(A_160,B_161,C_162)
      | ~ m1_subset_1(C_162,u1_struct_0(A_160))
      | ~ m1_subset_1(B_161,u1_struct_0(A_160))
      | ~ l3_lattices(A_160)
      | ~ v9_lattices(A_160)
      | ~ v8_lattices(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_1814,plain,
    ( k2_lattices('#skF_9','#skF_12','#skF_12') = '#skF_12'
    | ~ m1_subset_1('#skF_12',u1_struct_0('#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_427,c_1802])).

tff(c_1839,plain,
    ( k2_lattices('#skF_9','#skF_12','#skF_12') = '#skF_12'
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_184,c_80,c_74,c_1814])).

tff(c_1840,plain,(
    k2_lattices('#skF_9','#skF_12','#skF_12') = '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1839])).

tff(c_2601,plain,(
    ! [A_173,B_174,C_175,D_176] :
      ( k1_lattices(A_173,k2_lattices(A_173,B_174,C_175),k2_lattices(A_173,B_174,D_176)) = k2_lattices(A_173,B_174,k1_lattices(A_173,C_175,D_176))
      | ~ m1_subset_1(D_176,u1_struct_0(A_173))
      | ~ m1_subset_1(C_175,u1_struct_0(A_173))
      | ~ m1_subset_1(B_174,u1_struct_0(A_173))
      | ~ v11_lattices(A_173)
      | ~ l3_lattices(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2644,plain,(
    ! [D_176] :
      ( k2_lattices('#skF_9','#skF_12',k1_lattices('#skF_9','#skF_12',D_176)) = k1_lattices('#skF_9','#skF_12',k2_lattices('#skF_9','#skF_12',D_176))
      | ~ m1_subset_1(D_176,u1_struct_0('#skF_9'))
      | ~ m1_subset_1('#skF_12',u1_struct_0('#skF_9'))
      | ~ m1_subset_1('#skF_12',u1_struct_0('#skF_9'))
      | ~ v11_lattices('#skF_9')
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1840,c_2601])).

tff(c_2688,plain,(
    ! [D_176] :
      ( k2_lattices('#skF_9','#skF_12',k1_lattices('#skF_9','#skF_12',D_176)) = k1_lattices('#skF_9','#skF_12',k2_lattices('#skF_9','#skF_12',D_176))
      | ~ m1_subset_1(D_176,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_82,c_74,c_74,c_2644])).

tff(c_5763,plain,(
    ! [D_206] :
      ( k2_lattices('#skF_9','#skF_12',k1_lattices('#skF_9','#skF_12',D_206)) = k1_lattices('#skF_9','#skF_12',k2_lattices('#skF_9','#skF_12',D_206))
      | ~ m1_subset_1(D_206,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2688])).

tff(c_5858,plain,(
    k2_lattices('#skF_9','#skF_12',k1_lattices('#skF_9','#skF_12','#skF_10')) = k1_lattices('#skF_9','#skF_12',k2_lattices('#skF_9','#skF_12','#skF_10')) ),
    inference(resolution,[status(thm)],[c_78,c_5763])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_583,plain,(
    ! [A_140,B_141,C_142] :
      ( k3_lattices(A_140,B_141,C_142) = k1_lattices(A_140,B_141,C_142)
      | ~ m1_subset_1(C_142,u1_struct_0(A_140))
      | ~ m1_subset_1(B_141,u1_struct_0(A_140))
      | ~ l2_lattices(A_140)
      | ~ v4_lattices(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_609,plain,(
    ! [B_141] :
      ( k3_lattices('#skF_9',B_141,'#skF_12') = k1_lattices('#skF_9',B_141,'#skF_12')
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_9'))
      | ~ l2_lattices('#skF_9')
      | ~ v4_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_74,c_583])).

tff(c_633,plain,(
    ! [B_141] :
      ( k3_lattices('#skF_9',B_141,'#skF_12') = k1_lattices('#skF_9',B_141,'#skF_12')
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_9'))
      | ~ v4_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_609])).

tff(c_634,plain,(
    ! [B_141] :
      ( k3_lattices('#skF_9',B_141,'#skF_12') = k1_lattices('#skF_9',B_141,'#skF_12')
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_9'))
      | ~ v4_lattices('#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_633])).

tff(c_3637,plain,(
    ~ v4_lattices('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_634])).

tff(c_3640,plain,
    ( ~ v10_lattices('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l3_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_12,c_3637])).

tff(c_3643,plain,(
    v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_84,c_3640])).

tff(c_3645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3643])).

tff(c_3647,plain,(
    v4_lattices('#skF_9') ),
    inference(splitRight,[status(thm)],[c_634])).

tff(c_605,plain,(
    ! [B_141] :
      ( k3_lattices('#skF_9',B_141,'#skF_10') = k1_lattices('#skF_9',B_141,'#skF_10')
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_9'))
      | ~ l2_lattices('#skF_9')
      | ~ v4_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_78,c_583])).

tff(c_625,plain,(
    ! [B_141] :
      ( k3_lattices('#skF_9',B_141,'#skF_10') = k1_lattices('#skF_9',B_141,'#skF_10')
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_9'))
      | ~ v4_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_605])).

tff(c_626,plain,(
    ! [B_141] :
      ( k3_lattices('#skF_9',B_141,'#skF_10') = k1_lattices('#skF_9',B_141,'#skF_10')
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_9'))
      | ~ v4_lattices('#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_625])).

tff(c_4214,plain,(
    ! [B_188] :
      ( k3_lattices('#skF_9',B_188,'#skF_10') = k1_lattices('#skF_9',B_188,'#skF_10')
      | ~ m1_subset_1(B_188,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3647,c_626])).

tff(c_4309,plain,(
    k3_lattices('#skF_9','#skF_12','#skF_10') = k1_lattices('#skF_9','#skF_12','#skF_10') ),
    inference(resolution,[status(thm)],[c_74,c_4214])).

tff(c_3649,plain,(
    ! [B_183] :
      ( k3_lattices('#skF_9',B_183,'#skF_12') = k1_lattices('#skF_9',B_183,'#skF_12')
      | ~ m1_subset_1(B_183,u1_struct_0('#skF_9')) ) ),
    inference(splitRight,[status(thm)],[c_634])).

tff(c_3741,plain,(
    k3_lattices('#skF_9','#skF_10','#skF_12') = k1_lattices('#skF_9','#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_78,c_3649])).

tff(c_799,plain,(
    ! [A_147,C_148,B_149] :
      ( k3_lattices(A_147,C_148,B_149) = k3_lattices(A_147,B_149,C_148)
      | ~ m1_subset_1(C_148,u1_struct_0(A_147))
      | ~ m1_subset_1(B_149,u1_struct_0(A_147))
      | ~ l2_lattices(A_147)
      | ~ v4_lattices(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_825,plain,(
    ! [B_149] :
      ( k3_lattices('#skF_9',B_149,'#skF_12') = k3_lattices('#skF_9','#skF_12',B_149)
      | ~ m1_subset_1(B_149,u1_struct_0('#skF_9'))
      | ~ l2_lattices('#skF_9')
      | ~ v4_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_74,c_799])).

tff(c_849,plain,(
    ! [B_149] :
      ( k3_lattices('#skF_9',B_149,'#skF_12') = k3_lattices('#skF_9','#skF_12',B_149)
      | ~ m1_subset_1(B_149,u1_struct_0('#skF_9'))
      | ~ v4_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_825])).

tff(c_850,plain,(
    ! [B_149] :
      ( k3_lattices('#skF_9',B_149,'#skF_12') = k3_lattices('#skF_9','#skF_12',B_149)
      | ~ m1_subset_1(B_149,u1_struct_0('#skF_9'))
      | ~ v4_lattices('#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_849])).

tff(c_3764,plain,(
    ! [B_184] :
      ( k3_lattices('#skF_9',B_184,'#skF_12') = k3_lattices('#skF_9','#skF_12',B_184)
      | ~ m1_subset_1(B_184,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3647,c_850])).

tff(c_3809,plain,(
    k3_lattices('#skF_9','#skF_10','#skF_12') = k3_lattices('#skF_9','#skF_12','#skF_10') ),
    inference(resolution,[status(thm)],[c_78,c_3764])).

tff(c_3855,plain,(
    k3_lattices('#skF_9','#skF_12','#skF_10') = k1_lattices('#skF_9','#skF_10','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3741,c_3809])).

tff(c_4310,plain,(
    k1_lattices('#skF_9','#skF_10','#skF_12') = k1_lattices('#skF_9','#skF_12','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4309,c_3855])).

tff(c_87,plain,(
    ! [A_109] :
      ( l1_lattices(A_109)
      | ~ l3_lattices(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_91,plain,(
    l1_lattices('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_87])).

tff(c_1057,plain,(
    ! [A_152,B_153,C_154] :
      ( k4_lattices(A_152,B_153,C_154) = k2_lattices(A_152,B_153,C_154)
      | ~ m1_subset_1(C_154,u1_struct_0(A_152))
      | ~ m1_subset_1(B_153,u1_struct_0(A_152))
      | ~ l1_lattices(A_152)
      | ~ v6_lattices(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_1083,plain,(
    ! [B_153] :
      ( k4_lattices('#skF_9',B_153,'#skF_12') = k2_lattices('#skF_9',B_153,'#skF_12')
      | ~ m1_subset_1(B_153,u1_struct_0('#skF_9'))
      | ~ l1_lattices('#skF_9')
      | ~ v6_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_74,c_1057])).

tff(c_1107,plain,(
    ! [B_153] :
      ( k4_lattices('#skF_9',B_153,'#skF_12') = k2_lattices('#skF_9',B_153,'#skF_12')
      | ~ m1_subset_1(B_153,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_91,c_1083])).

tff(c_2166,plain,(
    ! [B_168] :
      ( k4_lattices('#skF_9',B_168,'#skF_12') = k2_lattices('#skF_9',B_168,'#skF_12')
      | ~ m1_subset_1(B_168,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1107])).

tff(c_2264,plain,(
    k4_lattices('#skF_9','#skF_10','#skF_12') = k2_lattices('#skF_9','#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_78,c_2166])).

tff(c_1079,plain,(
    ! [B_153] :
      ( k4_lattices('#skF_9',B_153,'#skF_10') = k2_lattices('#skF_9',B_153,'#skF_10')
      | ~ m1_subset_1(B_153,u1_struct_0('#skF_9'))
      | ~ l1_lattices('#skF_9')
      | ~ v6_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_78,c_1057])).

tff(c_1099,plain,(
    ! [B_153] :
      ( k4_lattices('#skF_9',B_153,'#skF_10') = k2_lattices('#skF_9',B_153,'#skF_10')
      | ~ m1_subset_1(B_153,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_91,c_1079])).

tff(c_1113,plain,(
    ! [B_155] :
      ( k4_lattices('#skF_9',B_155,'#skF_10') = k2_lattices('#skF_9',B_155,'#skF_10')
      | ~ m1_subset_1(B_155,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1099])).

tff(c_1201,plain,(
    k4_lattices('#skF_9','#skF_12','#skF_10') = k2_lattices('#skF_9','#skF_12','#skF_10') ),
    inference(resolution,[status(thm)],[c_74,c_1113])).

tff(c_1376,plain,(
    ! [A_156,C_157,B_158] :
      ( k4_lattices(A_156,C_157,B_158) = k4_lattices(A_156,B_158,C_157)
      | ~ m1_subset_1(C_157,u1_struct_0(A_156))
      | ~ m1_subset_1(B_158,u1_struct_0(A_156))
      | ~ l1_lattices(A_156)
      | ~ v6_lattices(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1402,plain,(
    ! [B_158] :
      ( k4_lattices('#skF_9',B_158,'#skF_10') = k4_lattices('#skF_9','#skF_10',B_158)
      | ~ m1_subset_1(B_158,u1_struct_0('#skF_9'))
      | ~ l1_lattices('#skF_9')
      | ~ v6_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_78,c_1376])).

tff(c_1430,plain,(
    ! [B_158] :
      ( k4_lattices('#skF_9',B_158,'#skF_10') = k4_lattices('#skF_9','#skF_10',B_158)
      | ~ m1_subset_1(B_158,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_91,c_1402])).

tff(c_2744,plain,(
    ! [B_177] :
      ( k4_lattices('#skF_9',B_177,'#skF_10') = k4_lattices('#skF_9','#skF_10',B_177)
      | ~ m1_subset_1(B_177,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1430])).

tff(c_2804,plain,(
    k4_lattices('#skF_9','#skF_10','#skF_12') = k4_lattices('#skF_9','#skF_12','#skF_10') ),
    inference(resolution,[status(thm)],[c_74,c_2744])).

tff(c_2851,plain,(
    k2_lattices('#skF_9','#skF_10','#skF_12') = k2_lattices('#skF_9','#skF_12','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2264,c_1201,c_2804])).

tff(c_639,plain,(
    ! [A_143,B_144,C_145] :
      ( k1_lattices(A_143,k2_lattices(A_143,B_144,C_145),C_145) = C_145
      | ~ m1_subset_1(C_145,u1_struct_0(A_143))
      | ~ m1_subset_1(B_144,u1_struct_0(A_143))
      | ~ v8_lattices(A_143)
      | ~ l3_lattices(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_665,plain,(
    ! [B_144] :
      ( k1_lattices('#skF_9',k2_lattices('#skF_9',B_144,'#skF_12'),'#skF_12') = '#skF_12'
      | ~ m1_subset_1(B_144,u1_struct_0('#skF_9'))
      | ~ v8_lattices('#skF_9')
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_74,c_639])).

tff(c_689,plain,(
    ! [B_144] :
      ( k1_lattices('#skF_9',k2_lattices('#skF_9',B_144,'#skF_12'),'#skF_12') = '#skF_12'
      | ~ m1_subset_1(B_144,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_196,c_665])).

tff(c_851,plain,(
    ! [B_150] :
      ( k1_lattices('#skF_9',k2_lattices('#skF_9',B_150,'#skF_12'),'#skF_12') = '#skF_12'
      | ~ m1_subset_1(B_150,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_689])).

tff(c_937,plain,(
    k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_10','#skF_12'),'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_78,c_851])).

tff(c_2902,plain,(
    k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_12','#skF_10'),'#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2851,c_937])).

tff(c_2647,plain,(
    ! [C_175] :
      ( k2_lattices('#skF_9','#skF_12',k1_lattices('#skF_9',C_175,'#skF_12')) = k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_12',C_175),'#skF_12')
      | ~ m1_subset_1('#skF_12',u1_struct_0('#skF_9'))
      | ~ m1_subset_1(C_175,u1_struct_0('#skF_9'))
      | ~ m1_subset_1('#skF_12',u1_struct_0('#skF_9'))
      | ~ v11_lattices('#skF_9')
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1840,c_2601])).

tff(c_2691,plain,(
    ! [C_175] :
      ( k2_lattices('#skF_9','#skF_12',k1_lattices('#skF_9',C_175,'#skF_12')) = k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_12',C_175),'#skF_12')
      | ~ m1_subset_1(C_175,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_82,c_74,c_74,c_2647])).

tff(c_6969,plain,(
    ! [C_224] :
      ( k2_lattices('#skF_9','#skF_12',k1_lattices('#skF_9',C_224,'#skF_12')) = k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_12',C_224),'#skF_12')
      | ~ m1_subset_1(C_224,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2691])).

tff(c_7017,plain,(
    k2_lattices('#skF_9','#skF_12',k1_lattices('#skF_9','#skF_10','#skF_12')) = k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_12','#skF_10'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_78,c_6969])).

tff(c_7066,plain,(
    k1_lattices('#skF_9','#skF_12',k2_lattices('#skF_9','#skF_12','#skF_10')) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5858,c_4310,c_2902,c_7017])).

tff(c_7072,plain,(
    k2_lattices('#skF_9','#skF_12',k1_lattices('#skF_9','#skF_12','#skF_10')) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7066,c_5858])).

tff(c_70,plain,(
    k3_lattices('#skF_9','#skF_10','#skF_11') = k3_lattices('#skF_9','#skF_10','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_3749,plain,(
    k3_lattices('#skF_9','#skF_10','#skF_11') = k1_lattices('#skF_9','#skF_10','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3741,c_70])).

tff(c_821,plain,(
    ! [B_149] :
      ( k3_lattices('#skF_9',B_149,'#skF_10') = k3_lattices('#skF_9','#skF_10',B_149)
      | ~ m1_subset_1(B_149,u1_struct_0('#skF_9'))
      | ~ l2_lattices('#skF_9')
      | ~ v4_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_78,c_799])).

tff(c_841,plain,(
    ! [B_149] :
      ( k3_lattices('#skF_9',B_149,'#skF_10') = k3_lattices('#skF_9','#skF_10',B_149)
      | ~ m1_subset_1(B_149,u1_struct_0('#skF_9'))
      | ~ v4_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_821])).

tff(c_842,plain,(
    ! [B_149] :
      ( k3_lattices('#skF_9',B_149,'#skF_10') = k3_lattices('#skF_9','#skF_10',B_149)
      | ~ m1_subset_1(B_149,u1_struct_0('#skF_9'))
      | ~ v4_lattices('#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_841])).

tff(c_3883,plain,(
    ! [B_185] :
      ( k3_lattices('#skF_9',B_185,'#skF_10') = k3_lattices('#skF_9','#skF_10',B_185)
      | ~ m1_subset_1(B_185,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3647,c_842])).

tff(c_3931,plain,(
    k3_lattices('#skF_9','#skF_11','#skF_10') = k3_lattices('#skF_9','#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_76,c_3883])).

tff(c_3976,plain,(
    k3_lattices('#skF_9','#skF_11','#skF_10') = k1_lattices('#skF_9','#skF_10','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3749,c_3931])).

tff(c_4262,plain,(
    k3_lattices('#skF_9','#skF_11','#skF_10') = k1_lattices('#skF_9','#skF_11','#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_4214])).

tff(c_4308,plain,(
    k1_lattices('#skF_9','#skF_11','#skF_10') = k1_lattices('#skF_9','#skF_10','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3976,c_4262])).

tff(c_4325,plain,(
    k1_lattices('#skF_9','#skF_11','#skF_10') = k1_lattices('#skF_9','#skF_12','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4310,c_4308])).

tff(c_607,plain,(
    ! [B_141] :
      ( k3_lattices('#skF_9',B_141,'#skF_11') = k1_lattices('#skF_9',B_141,'#skF_11')
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_9'))
      | ~ l2_lattices('#skF_9')
      | ~ v4_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_76,c_583])).

tff(c_629,plain,(
    ! [B_141] :
      ( k3_lattices('#skF_9',B_141,'#skF_11') = k1_lattices('#skF_9',B_141,'#skF_11')
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_9'))
      | ~ v4_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_607])).

tff(c_630,plain,(
    ! [B_141] :
      ( k3_lattices('#skF_9',B_141,'#skF_11') = k1_lattices('#skF_9',B_141,'#skF_11')
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_9'))
      | ~ v4_lattices('#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_629])).

tff(c_3985,plain,(
    ! [B_186] :
      ( k3_lattices('#skF_9',B_186,'#skF_11') = k1_lattices('#skF_9',B_186,'#skF_11')
      | ~ m1_subset_1(B_186,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3647,c_630])).

tff(c_4030,plain,(
    k3_lattices('#skF_9','#skF_10','#skF_11') = k1_lattices('#skF_9','#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_78,c_3985])).

tff(c_4078,plain,(
    k1_lattices('#skF_9','#skF_10','#skF_11') = k1_lattices('#skF_9','#skF_10','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3749,c_4030])).

tff(c_4327,plain,(
    k1_lattices('#skF_9','#skF_10','#skF_11') = k1_lattices('#skF_9','#skF_12','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4310,c_4078])).

tff(c_1081,plain,(
    ! [B_153] :
      ( k4_lattices('#skF_9',B_153,'#skF_11') = k2_lattices('#skF_9',B_153,'#skF_11')
      | ~ m1_subset_1(B_153,u1_struct_0('#skF_9'))
      | ~ l1_lattices('#skF_9')
      | ~ v6_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_76,c_1057])).

tff(c_1103,plain,(
    ! [B_153] :
      ( k4_lattices('#skF_9',B_153,'#skF_11') = k2_lattices('#skF_9',B_153,'#skF_11')
      | ~ m1_subset_1(B_153,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_91,c_1081])).

tff(c_1522,plain,(
    ! [B_159] :
      ( k4_lattices('#skF_9',B_159,'#skF_11') = k2_lattices('#skF_9',B_159,'#skF_11')
      | ~ m1_subset_1(B_159,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1103])).

tff(c_1620,plain,(
    k4_lattices('#skF_9','#skF_10','#skF_11') = k2_lattices('#skF_9','#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_78,c_1522])).

tff(c_72,plain,(
    k4_lattices('#skF_9','#skF_10','#skF_11') = k4_lattices('#skF_9','#skF_10','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_1623,plain,(
    k4_lattices('#skF_9','#skF_10','#skF_12') = k2_lattices('#skF_9','#skF_10','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_72])).

tff(c_2348,plain,(
    k2_lattices('#skF_9','#skF_10','#skF_11') = k2_lattices('#skF_9','#skF_10','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2264,c_1623])).

tff(c_663,plain,(
    ! [B_144] :
      ( k1_lattices('#skF_9',k2_lattices('#skF_9',B_144,'#skF_11'),'#skF_11') = '#skF_11'
      | ~ m1_subset_1(B_144,u1_struct_0('#skF_9'))
      | ~ v8_lattices('#skF_9')
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_76,c_639])).

tff(c_685,plain,(
    ! [B_144] :
      ( k1_lattices('#skF_9',k2_lattices('#skF_9',B_144,'#skF_11'),'#skF_11') = '#skF_11'
      | ~ m1_subset_1(B_144,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_196,c_663])).

tff(c_956,plain,(
    ! [B_151] :
      ( k1_lattices('#skF_9',k2_lattices('#skF_9',B_151,'#skF_11'),'#skF_11') = '#skF_11'
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_685])).

tff(c_1042,plain,(
    k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_10','#skF_11'),'#skF_11') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_78,c_956])).

tff(c_2583,plain,(
    k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_10','#skF_12'),'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2348,c_1042])).

tff(c_2895,plain,(
    k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_12','#skF_10'),'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2851,c_2583])).

tff(c_2582,plain,(
    k4_lattices('#skF_9','#skF_10','#skF_11') = k2_lattices('#skF_9','#skF_10','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2348,c_1620])).

tff(c_1200,plain,(
    k4_lattices('#skF_9','#skF_11','#skF_10') = k2_lattices('#skF_9','#skF_11','#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_1113])).

tff(c_2801,plain,(
    k4_lattices('#skF_9','#skF_11','#skF_10') = k4_lattices('#skF_9','#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_76,c_2744])).

tff(c_2849,plain,(
    k2_lattices('#skF_9','#skF_11','#skF_10') = k2_lattices('#skF_9','#skF_10','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2582,c_1200,c_2801])).

tff(c_2891,plain,(
    k2_lattices('#skF_9','#skF_11','#skF_10') = k2_lattices('#skF_9','#skF_12','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2851,c_2849])).

tff(c_140,plain,
    ( k1_lattices('#skF_9','#skF_11','#skF_11') = '#skF_11'
    | ~ l3_lattices('#skF_9')
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | ~ v6_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_120])).

tff(c_157,plain,
    ( k1_lattices('#skF_9','#skF_11','#skF_11') = '#skF_11'
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | ~ v6_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_140])).

tff(c_158,plain,
    ( k1_lattices('#skF_9','#skF_11','#skF_11') = '#skF_11'
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | ~ v6_lattices('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_157])).

tff(c_257,plain,(
    k1_lattices('#skF_9','#skF_11','#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_196,c_184,c_158])).

tff(c_229,plain,(
    ! [B_132] :
      ( r1_lattices('#skF_9',B_132,'#skF_11')
      | k1_lattices('#skF_9',B_132,'#skF_11') != '#skF_11'
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_9'))
      | ~ l2_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_76,c_209])).

tff(c_246,plain,(
    ! [B_132] :
      ( r1_lattices('#skF_9',B_132,'#skF_11')
      | k1_lattices('#skF_9',B_132,'#skF_11') != '#skF_11'
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_229])).

tff(c_485,plain,(
    ! [B_139] :
      ( r1_lattices('#skF_9',B_139,'#skF_11')
      | k1_lattices('#skF_9',B_139,'#skF_11') != '#skF_11'
      | ~ m1_subset_1(B_139,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_246])).

tff(c_530,plain,
    ( r1_lattices('#skF_9','#skF_11','#skF_11')
    | k1_lattices('#skF_9','#skF_11','#skF_11') != '#skF_11' ),
    inference(resolution,[status(thm)],[c_76,c_485])).

tff(c_574,plain,(
    r1_lattices('#skF_9','#skF_11','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_530])).

tff(c_1812,plain,
    ( k2_lattices('#skF_9','#skF_11','#skF_11') = '#skF_11'
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_9'))
    | ~ l3_lattices('#skF_9')
    | ~ v9_lattices('#skF_9')
    | ~ v8_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_574,c_1802])).

tff(c_1835,plain,
    ( k2_lattices('#skF_9','#skF_11','#skF_11') = '#skF_11'
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_184,c_80,c_76,c_1812])).

tff(c_1836,plain,(
    k2_lattices('#skF_9','#skF_11','#skF_11') = '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1835])).

tff(c_2653,plain,(
    ! [C_175] :
      ( k2_lattices('#skF_9','#skF_11',k1_lattices('#skF_9',C_175,'#skF_11')) = k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_11',C_175),'#skF_11')
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_9'))
      | ~ m1_subset_1(C_175,u1_struct_0('#skF_9'))
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_9'))
      | ~ v11_lattices('#skF_9')
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1836,c_2601])).

tff(c_2697,plain,(
    ! [C_175] :
      ( k2_lattices('#skF_9','#skF_11',k1_lattices('#skF_9',C_175,'#skF_11')) = k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_11',C_175),'#skF_11')
      | ~ m1_subset_1(C_175,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_82,c_76,c_76,c_2653])).

tff(c_6825,plain,(
    ! [C_221] :
      ( k2_lattices('#skF_9','#skF_11',k1_lattices('#skF_9',C_221,'#skF_11')) = k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_11',C_221),'#skF_11')
      | ~ m1_subset_1(C_221,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2697])).

tff(c_6873,plain,(
    k2_lattices('#skF_9','#skF_11',k1_lattices('#skF_9','#skF_10','#skF_11')) = k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_11','#skF_10'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_78,c_6825])).

tff(c_6922,plain,(
    k2_lattices('#skF_9','#skF_11',k1_lattices('#skF_9','#skF_12','#skF_10')) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4327,c_2895,c_2891,c_6873])).

tff(c_2265,plain,(
    k4_lattices('#skF_9','#skF_11','#skF_12') = k2_lattices('#skF_9','#skF_11','#skF_12') ),
    inference(resolution,[status(thm)],[c_76,c_2166])).

tff(c_1622,plain,(
    k4_lattices('#skF_9','#skF_12','#skF_11') = k2_lattices('#skF_9','#skF_12','#skF_11') ),
    inference(resolution,[status(thm)],[c_74,c_1522])).

tff(c_1404,plain,(
    ! [B_158] :
      ( k4_lattices('#skF_9',B_158,'#skF_11') = k4_lattices('#skF_9','#skF_11',B_158)
      | ~ m1_subset_1(B_158,u1_struct_0('#skF_9'))
      | ~ l1_lattices('#skF_9')
      | ~ v6_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_76,c_1376])).

tff(c_1434,plain,(
    ! [B_158] :
      ( k4_lattices('#skF_9',B_158,'#skF_11') = k4_lattices('#skF_9','#skF_11',B_158)
      | ~ m1_subset_1(B_158,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_91,c_1404])).

tff(c_2964,plain,(
    ! [B_178] :
      ( k4_lattices('#skF_9',B_178,'#skF_11') = k4_lattices('#skF_9','#skF_11',B_178)
      | ~ m1_subset_1(B_178,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1434])).

tff(c_3018,plain,(
    k4_lattices('#skF_9','#skF_11','#skF_12') = k4_lattices('#skF_9','#skF_12','#skF_11') ),
    inference(resolution,[status(thm)],[c_74,c_2964])).

tff(c_3063,plain,(
    k2_lattices('#skF_9','#skF_11','#skF_12') = k2_lattices('#skF_9','#skF_12','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2265,c_1622,c_3018])).

tff(c_20,plain,(
    ! [A_8,B_23,C_27,D_29] :
      ( k1_lattices(A_8,k2_lattices(A_8,B_23,C_27),k2_lattices(A_8,B_23,D_29)) = k2_lattices(A_8,B_23,k1_lattices(A_8,C_27,D_29))
      | ~ m1_subset_1(D_29,u1_struct_0(A_8))
      | ~ m1_subset_1(C_27,u1_struct_0(A_8))
      | ~ m1_subset_1(B_23,u1_struct_0(A_8))
      | ~ v11_lattices(A_8)
      | ~ l3_lattices(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2868,plain,(
    ! [C_27] :
      ( k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_11',C_27),k2_lattices('#skF_9','#skF_10','#skF_12')) = k2_lattices('#skF_9','#skF_11',k1_lattices('#skF_9',C_27,'#skF_10'))
      | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_9'))
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_9'))
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_9'))
      | ~ v11_lattices('#skF_9')
      | ~ l3_lattices('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2849,c_20])).

tff(c_2875,plain,(
    ! [C_27] :
      ( k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_11',C_27),k2_lattices('#skF_9','#skF_10','#skF_12')) = k2_lattices('#skF_9','#skF_11',k1_lattices('#skF_9',C_27,'#skF_10'))
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_82,c_76,c_78,c_2868])).

tff(c_2876,plain,(
    ! [C_27] :
      ( k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_11',C_27),k2_lattices('#skF_9','#skF_10','#skF_12')) = k2_lattices('#skF_9','#skF_11',k1_lattices('#skF_9',C_27,'#skF_10'))
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2875])).

tff(c_10409,plain,(
    ! [C_276] :
      ( k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_11',C_276),k2_lattices('#skF_9','#skF_12','#skF_10')) = k2_lattices('#skF_9','#skF_11',k1_lattices('#skF_9',C_276,'#skF_10'))
      | ~ m1_subset_1(C_276,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2851,c_2876])).

tff(c_10441,plain,
    ( k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_12','#skF_11'),k2_lattices('#skF_9','#skF_12','#skF_10')) = k2_lattices('#skF_9','#skF_11',k1_lattices('#skF_9','#skF_12','#skF_10'))
    | ~ m1_subset_1('#skF_12',u1_struct_0('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3063,c_10409])).

tff(c_10460,plain,(
    k1_lattices('#skF_9',k2_lattices('#skF_9','#skF_12','#skF_11'),k2_lattices('#skF_9','#skF_12','#skF_10')) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6922,c_10441])).

tff(c_10468,plain,
    ( k2_lattices('#skF_9','#skF_12',k1_lattices('#skF_9','#skF_11','#skF_10')) = '#skF_11'
    | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_9'))
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_9'))
    | ~ m1_subset_1('#skF_12',u1_struct_0('#skF_9'))
    | ~ v11_lattices('#skF_9')
    | ~ l3_lattices('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_10460,c_20])).

tff(c_10475,plain,
    ( '#skF_11' = '#skF_12'
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_82,c_74,c_76,c_78,c_7072,c_4325,c_10468])).

tff(c_10477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_68,c_10475])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.51/3.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.85/3.13  
% 8.85/3.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.85/3.13  %$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v11_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_7 > #skF_5 > #skF_2 > #skF_4 > #skF_11 > #skF_1 > #skF_8 > #skF_10 > #skF_9 > #skF_3 > #skF_6 > #skF_12
% 8.85/3.13  
% 8.85/3.13  %Foreground sorts:
% 8.85/3.13  
% 8.85/3.13  
% 8.85/3.13  %Background operators:
% 8.85/3.13  
% 8.85/3.13  
% 8.85/3.13  %Foreground operators:
% 8.85/3.13  tff(l3_lattices, type, l3_lattices: $i > $o).
% 8.85/3.13  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 8.85/3.13  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.85/3.13  tff('#skF_7', type, '#skF_7': $i > $i).
% 8.85/3.13  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 8.85/3.13  tff('#skF_5', type, '#skF_5': $i > $i).
% 8.85/3.13  tff(l2_lattices, type, l2_lattices: $i > $o).
% 8.85/3.13  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.85/3.13  tff('#skF_4', type, '#skF_4': $i > $i).
% 8.85/3.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.85/3.13  tff('#skF_11', type, '#skF_11': $i).
% 8.85/3.13  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 8.85/3.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.85/3.13  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 8.85/3.13  tff(l1_lattices, type, l1_lattices: $i > $o).
% 8.85/3.13  tff('#skF_8', type, '#skF_8': $i > $i).
% 8.85/3.13  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 8.85/3.13  tff('#skF_10', type, '#skF_10': $i).
% 8.85/3.13  tff(v4_lattices, type, v4_lattices: $i > $o).
% 8.85/3.13  tff(v6_lattices, type, v6_lattices: $i > $o).
% 8.85/3.13  tff(v9_lattices, type, v9_lattices: $i > $o).
% 8.85/3.13  tff(v5_lattices, type, v5_lattices: $i > $o).
% 8.85/3.13  tff(v10_lattices, type, v10_lattices: $i > $o).
% 8.85/3.13  tff('#skF_9', type, '#skF_9': $i).
% 8.85/3.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.85/3.13  tff(v11_lattices, type, v11_lattices: $i > $o).
% 8.85/3.13  tff('#skF_3', type, '#skF_3': $i > $i).
% 8.85/3.13  tff(v8_lattices, type, v8_lattices: $i > $o).
% 8.85/3.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.85/3.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.85/3.13  tff('#skF_6', type, '#skF_6': $i > $i).
% 8.85/3.13  tff('#skF_12', type, '#skF_12': $i).
% 8.85/3.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.85/3.13  tff(v7_lattices, type, v7_lattices: $i > $o).
% 8.85/3.13  
% 8.85/3.16  tff(f_244, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v11_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((k4_lattices(A, B, C) = k4_lattices(A, B, D)) & (k3_lattices(A, B, C) = k3_lattices(A, B, D))) => (C = D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_lattices)).
% 8.85/3.16  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 8.85/3.16  tff(f_200, axiom, (![A]: (((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k1_lattices(A, B, B) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_lattices)).
% 8.85/3.16  tff(f_158, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 8.85/3.16  tff(f_106, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 8.85/3.16  tff(f_219, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 8.85/3.16  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v11_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, C, D)) = k1_lattices(A, k2_lattices(A, B, C), k2_lattices(A, B, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_lattices)).
% 8.85/3.16  tff(f_171, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 8.85/3.16  tff(f_60, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k3_lattices(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_lattices)).
% 8.85/3.16  tff(f_184, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 8.85/3.16  tff(f_73, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k4_lattices(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 8.85/3.16  tff(f_139, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 8.85/3.16  tff(c_86, plain, (~v2_struct_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.85/3.16  tff(c_68, plain, ('#skF_11'!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.85/3.16  tff(c_80, plain, (l3_lattices('#skF_9')), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.85/3.16  tff(c_82, plain, (v11_lattices('#skF_9')), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.85/3.16  tff(c_74, plain, (m1_subset_1('#skF_12', u1_struct_0('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.85/3.16  tff(c_76, plain, (m1_subset_1('#skF_11', u1_struct_0('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.85/3.16  tff(c_78, plain, (m1_subset_1('#skF_10', u1_struct_0('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.85/3.16  tff(c_84, plain, (v10_lattices('#skF_9')), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.85/3.16  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.85/3.16  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.85/3.16  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.85/3.16  tff(c_120, plain, (![A_126, B_127]: (k1_lattices(A_126, B_127, B_127)=B_127 | ~m1_subset_1(B_127, u1_struct_0(A_126)) | ~l3_lattices(A_126) | ~v9_lattices(A_126) | ~v8_lattices(A_126) | ~v6_lattices(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_200])).
% 8.85/3.16  tff(c_138, plain, (k1_lattices('#skF_9', '#skF_10', '#skF_10')='#skF_10' | ~l3_lattices('#skF_9') | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_78, c_120])).
% 8.85/3.16  tff(c_153, plain, (k1_lattices('#skF_9', '#skF_10', '#skF_10')='#skF_10' | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_138])).
% 8.85/3.16  tff(c_154, plain, (k1_lattices('#skF_9', '#skF_10', '#skF_10')='#skF_10' | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_86, c_153])).
% 8.85/3.16  tff(c_163, plain, (~v6_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_154])).
% 8.85/3.16  tff(c_166, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_8, c_163])).
% 8.85/3.16  tff(c_169, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_84, c_166])).
% 8.85/3.16  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_169])).
% 8.85/3.16  tff(c_172, plain, (~v8_lattices('#skF_9') | ~v9_lattices('#skF_9') | k1_lattices('#skF_9', '#skF_10', '#skF_10')='#skF_10'), inference(splitRight, [status(thm)], [c_154])).
% 8.85/3.16  tff(c_174, plain, (~v9_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_172])).
% 8.85/3.16  tff(c_177, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_2, c_174])).
% 8.85/3.16  tff(c_180, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_84, c_177])).
% 8.85/3.16  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_180])).
% 8.85/3.16  tff(c_183, plain, (~v8_lattices('#skF_9') | k1_lattices('#skF_9', '#skF_10', '#skF_10')='#skF_10'), inference(splitRight, [status(thm)], [c_172])).
% 8.85/3.16  tff(c_186, plain, (~v8_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_183])).
% 8.85/3.16  tff(c_189, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_4, c_186])).
% 8.85/3.16  tff(c_192, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_84, c_189])).
% 8.85/3.16  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_192])).
% 8.85/3.16  tff(c_196, plain, (v8_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_183])).
% 8.85/3.16  tff(c_184, plain, (v9_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_172])).
% 8.85/3.16  tff(c_173, plain, (v6_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_154])).
% 8.85/3.16  tff(c_142, plain, (k1_lattices('#skF_9', '#skF_12', '#skF_12')='#skF_12' | ~l3_lattices('#skF_9') | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_74, c_120])).
% 8.85/3.16  tff(c_161, plain, (k1_lattices('#skF_9', '#skF_12', '#skF_12')='#skF_12' | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_142])).
% 8.85/3.16  tff(c_162, plain, (k1_lattices('#skF_9', '#skF_12', '#skF_12')='#skF_12' | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_86, c_161])).
% 8.85/3.16  tff(c_198, plain, (k1_lattices('#skF_9', '#skF_12', '#skF_12')='#skF_12' | ~v8_lattices('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_184, c_162])).
% 8.85/3.16  tff(c_199, plain, (~v8_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_198])).
% 8.85/3.16  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_196, c_199])).
% 8.85/3.16  tff(c_202, plain, (k1_lattices('#skF_9', '#skF_12', '#skF_12')='#skF_12'), inference(splitRight, [status(thm)], [c_198])).
% 8.85/3.16  tff(c_92, plain, (![A_110]: (l2_lattices(A_110) | ~l3_lattices(A_110))), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.85/3.16  tff(c_96, plain, (l2_lattices('#skF_9')), inference(resolution, [status(thm)], [c_80, c_92])).
% 8.85/3.16  tff(c_209, plain, (![A_131, B_132, C_133]: (r1_lattices(A_131, B_132, C_133) | k1_lattices(A_131, B_132, C_133)!=C_133 | ~m1_subset_1(C_133, u1_struct_0(A_131)) | ~m1_subset_1(B_132, u1_struct_0(A_131)) | ~l2_lattices(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.85/3.16  tff(c_231, plain, (![B_132]: (r1_lattices('#skF_9', B_132, '#skF_12') | k1_lattices('#skF_9', B_132, '#skF_12')!='#skF_12' | ~m1_subset_1(B_132, u1_struct_0('#skF_9')) | ~l2_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_74, c_209])).
% 8.85/3.16  tff(c_250, plain, (![B_132]: (r1_lattices('#skF_9', B_132, '#skF_12') | k1_lattices('#skF_9', B_132, '#skF_12')!='#skF_12' | ~m1_subset_1(B_132, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_231])).
% 8.85/3.16  tff(c_349, plain, (![B_135]: (r1_lattices('#skF_9', B_135, '#skF_12') | k1_lattices('#skF_9', B_135, '#skF_12')!='#skF_12' | ~m1_subset_1(B_135, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_86, c_250])).
% 8.85/3.16  tff(c_390, plain, (r1_lattices('#skF_9', '#skF_12', '#skF_12') | k1_lattices('#skF_9', '#skF_12', '#skF_12')!='#skF_12'), inference(resolution, [status(thm)], [c_74, c_349])).
% 8.85/3.16  tff(c_427, plain, (r1_lattices('#skF_9', '#skF_12', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_202, c_390])).
% 8.85/3.16  tff(c_1802, plain, (![A_160, B_161, C_162]: (k2_lattices(A_160, B_161, C_162)=B_161 | ~r1_lattices(A_160, B_161, C_162) | ~m1_subset_1(C_162, u1_struct_0(A_160)) | ~m1_subset_1(B_161, u1_struct_0(A_160)) | ~l3_lattices(A_160) | ~v9_lattices(A_160) | ~v8_lattices(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_219])).
% 8.85/3.16  tff(c_1814, plain, (k2_lattices('#skF_9', '#skF_12', '#skF_12')='#skF_12' | ~m1_subset_1('#skF_12', u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_427, c_1802])).
% 8.85/3.16  tff(c_1839, plain, (k2_lattices('#skF_9', '#skF_12', '#skF_12')='#skF_12' | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_184, c_80, c_74, c_1814])).
% 8.85/3.16  tff(c_1840, plain, (k2_lattices('#skF_9', '#skF_12', '#skF_12')='#skF_12'), inference(negUnitSimplification, [status(thm)], [c_86, c_1839])).
% 8.85/3.16  tff(c_2601, plain, (![A_173, B_174, C_175, D_176]: (k1_lattices(A_173, k2_lattices(A_173, B_174, C_175), k2_lattices(A_173, B_174, D_176))=k2_lattices(A_173, B_174, k1_lattices(A_173, C_175, D_176)) | ~m1_subset_1(D_176, u1_struct_0(A_173)) | ~m1_subset_1(C_175, u1_struct_0(A_173)) | ~m1_subset_1(B_174, u1_struct_0(A_173)) | ~v11_lattices(A_173) | ~l3_lattices(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.85/3.16  tff(c_2644, plain, (![D_176]: (k2_lattices('#skF_9', '#skF_12', k1_lattices('#skF_9', '#skF_12', D_176))=k1_lattices('#skF_9', '#skF_12', k2_lattices('#skF_9', '#skF_12', D_176)) | ~m1_subset_1(D_176, u1_struct_0('#skF_9')) | ~m1_subset_1('#skF_12', u1_struct_0('#skF_9')) | ~m1_subset_1('#skF_12', u1_struct_0('#skF_9')) | ~v11_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1840, c_2601])).
% 8.85/3.16  tff(c_2688, plain, (![D_176]: (k2_lattices('#skF_9', '#skF_12', k1_lattices('#skF_9', '#skF_12', D_176))=k1_lattices('#skF_9', '#skF_12', k2_lattices('#skF_9', '#skF_12', D_176)) | ~m1_subset_1(D_176, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_82, c_74, c_74, c_2644])).
% 8.85/3.16  tff(c_5763, plain, (![D_206]: (k2_lattices('#skF_9', '#skF_12', k1_lattices('#skF_9', '#skF_12', D_206))=k1_lattices('#skF_9', '#skF_12', k2_lattices('#skF_9', '#skF_12', D_206)) | ~m1_subset_1(D_206, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_86, c_2688])).
% 8.85/3.16  tff(c_5858, plain, (k2_lattices('#skF_9', '#skF_12', k1_lattices('#skF_9', '#skF_12', '#skF_10'))=k1_lattices('#skF_9', '#skF_12', k2_lattices('#skF_9', '#skF_12', '#skF_10'))), inference(resolution, [status(thm)], [c_78, c_5763])).
% 8.85/3.16  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.85/3.16  tff(c_583, plain, (![A_140, B_141, C_142]: (k3_lattices(A_140, B_141, C_142)=k1_lattices(A_140, B_141, C_142) | ~m1_subset_1(C_142, u1_struct_0(A_140)) | ~m1_subset_1(B_141, u1_struct_0(A_140)) | ~l2_lattices(A_140) | ~v4_lattices(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_171])).
% 8.85/3.16  tff(c_609, plain, (![B_141]: (k3_lattices('#skF_9', B_141, '#skF_12')=k1_lattices('#skF_9', B_141, '#skF_12') | ~m1_subset_1(B_141, u1_struct_0('#skF_9')) | ~l2_lattices('#skF_9') | ~v4_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_74, c_583])).
% 8.85/3.16  tff(c_633, plain, (![B_141]: (k3_lattices('#skF_9', B_141, '#skF_12')=k1_lattices('#skF_9', B_141, '#skF_12') | ~m1_subset_1(B_141, u1_struct_0('#skF_9')) | ~v4_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_609])).
% 8.85/3.16  tff(c_634, plain, (![B_141]: (k3_lattices('#skF_9', B_141, '#skF_12')=k1_lattices('#skF_9', B_141, '#skF_12') | ~m1_subset_1(B_141, u1_struct_0('#skF_9')) | ~v4_lattices('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_86, c_633])).
% 8.85/3.16  tff(c_3637, plain, (~v4_lattices('#skF_9')), inference(splitLeft, [status(thm)], [c_634])).
% 8.85/3.16  tff(c_3640, plain, (~v10_lattices('#skF_9') | v2_struct_0('#skF_9') | ~l3_lattices('#skF_9')), inference(resolution, [status(thm)], [c_12, c_3637])).
% 8.85/3.16  tff(c_3643, plain, (v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_84, c_3640])).
% 8.85/3.16  tff(c_3645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_3643])).
% 8.85/3.16  tff(c_3647, plain, (v4_lattices('#skF_9')), inference(splitRight, [status(thm)], [c_634])).
% 8.85/3.16  tff(c_605, plain, (![B_141]: (k3_lattices('#skF_9', B_141, '#skF_10')=k1_lattices('#skF_9', B_141, '#skF_10') | ~m1_subset_1(B_141, u1_struct_0('#skF_9')) | ~l2_lattices('#skF_9') | ~v4_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_78, c_583])).
% 8.85/3.16  tff(c_625, plain, (![B_141]: (k3_lattices('#skF_9', B_141, '#skF_10')=k1_lattices('#skF_9', B_141, '#skF_10') | ~m1_subset_1(B_141, u1_struct_0('#skF_9')) | ~v4_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_605])).
% 8.85/3.16  tff(c_626, plain, (![B_141]: (k3_lattices('#skF_9', B_141, '#skF_10')=k1_lattices('#skF_9', B_141, '#skF_10') | ~m1_subset_1(B_141, u1_struct_0('#skF_9')) | ~v4_lattices('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_86, c_625])).
% 8.85/3.16  tff(c_4214, plain, (![B_188]: (k3_lattices('#skF_9', B_188, '#skF_10')=k1_lattices('#skF_9', B_188, '#skF_10') | ~m1_subset_1(B_188, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_3647, c_626])).
% 8.85/3.16  tff(c_4309, plain, (k3_lattices('#skF_9', '#skF_12', '#skF_10')=k1_lattices('#skF_9', '#skF_12', '#skF_10')), inference(resolution, [status(thm)], [c_74, c_4214])).
% 8.85/3.16  tff(c_3649, plain, (![B_183]: (k3_lattices('#skF_9', B_183, '#skF_12')=k1_lattices('#skF_9', B_183, '#skF_12') | ~m1_subset_1(B_183, u1_struct_0('#skF_9')))), inference(splitRight, [status(thm)], [c_634])).
% 8.85/3.16  tff(c_3741, plain, (k3_lattices('#skF_9', '#skF_10', '#skF_12')=k1_lattices('#skF_9', '#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_78, c_3649])).
% 8.85/3.16  tff(c_799, plain, (![A_147, C_148, B_149]: (k3_lattices(A_147, C_148, B_149)=k3_lattices(A_147, B_149, C_148) | ~m1_subset_1(C_148, u1_struct_0(A_147)) | ~m1_subset_1(B_149, u1_struct_0(A_147)) | ~l2_lattices(A_147) | ~v4_lattices(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.85/3.16  tff(c_825, plain, (![B_149]: (k3_lattices('#skF_9', B_149, '#skF_12')=k3_lattices('#skF_9', '#skF_12', B_149) | ~m1_subset_1(B_149, u1_struct_0('#skF_9')) | ~l2_lattices('#skF_9') | ~v4_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_74, c_799])).
% 8.85/3.16  tff(c_849, plain, (![B_149]: (k3_lattices('#skF_9', B_149, '#skF_12')=k3_lattices('#skF_9', '#skF_12', B_149) | ~m1_subset_1(B_149, u1_struct_0('#skF_9')) | ~v4_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_825])).
% 8.85/3.16  tff(c_850, plain, (![B_149]: (k3_lattices('#skF_9', B_149, '#skF_12')=k3_lattices('#skF_9', '#skF_12', B_149) | ~m1_subset_1(B_149, u1_struct_0('#skF_9')) | ~v4_lattices('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_86, c_849])).
% 8.85/3.16  tff(c_3764, plain, (![B_184]: (k3_lattices('#skF_9', B_184, '#skF_12')=k3_lattices('#skF_9', '#skF_12', B_184) | ~m1_subset_1(B_184, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_3647, c_850])).
% 8.85/3.16  tff(c_3809, plain, (k3_lattices('#skF_9', '#skF_10', '#skF_12')=k3_lattices('#skF_9', '#skF_12', '#skF_10')), inference(resolution, [status(thm)], [c_78, c_3764])).
% 8.85/3.16  tff(c_3855, plain, (k3_lattices('#skF_9', '#skF_12', '#skF_10')=k1_lattices('#skF_9', '#skF_10', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_3741, c_3809])).
% 8.85/3.16  tff(c_4310, plain, (k1_lattices('#skF_9', '#skF_10', '#skF_12')=k1_lattices('#skF_9', '#skF_12', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_4309, c_3855])).
% 8.85/3.16  tff(c_87, plain, (![A_109]: (l1_lattices(A_109) | ~l3_lattices(A_109))), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.85/3.16  tff(c_91, plain, (l1_lattices('#skF_9')), inference(resolution, [status(thm)], [c_80, c_87])).
% 8.85/3.16  tff(c_1057, plain, (![A_152, B_153, C_154]: (k4_lattices(A_152, B_153, C_154)=k2_lattices(A_152, B_153, C_154) | ~m1_subset_1(C_154, u1_struct_0(A_152)) | ~m1_subset_1(B_153, u1_struct_0(A_152)) | ~l1_lattices(A_152) | ~v6_lattices(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_184])).
% 8.85/3.16  tff(c_1083, plain, (![B_153]: (k4_lattices('#skF_9', B_153, '#skF_12')=k2_lattices('#skF_9', B_153, '#skF_12') | ~m1_subset_1(B_153, u1_struct_0('#skF_9')) | ~l1_lattices('#skF_9') | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_74, c_1057])).
% 8.85/3.16  tff(c_1107, plain, (![B_153]: (k4_lattices('#skF_9', B_153, '#skF_12')=k2_lattices('#skF_9', B_153, '#skF_12') | ~m1_subset_1(B_153, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_91, c_1083])).
% 8.85/3.16  tff(c_2166, plain, (![B_168]: (k4_lattices('#skF_9', B_168, '#skF_12')=k2_lattices('#skF_9', B_168, '#skF_12') | ~m1_subset_1(B_168, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_86, c_1107])).
% 8.85/3.16  tff(c_2264, plain, (k4_lattices('#skF_9', '#skF_10', '#skF_12')=k2_lattices('#skF_9', '#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_78, c_2166])).
% 8.85/3.16  tff(c_1079, plain, (![B_153]: (k4_lattices('#skF_9', B_153, '#skF_10')=k2_lattices('#skF_9', B_153, '#skF_10') | ~m1_subset_1(B_153, u1_struct_0('#skF_9')) | ~l1_lattices('#skF_9') | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_78, c_1057])).
% 8.85/3.16  tff(c_1099, plain, (![B_153]: (k4_lattices('#skF_9', B_153, '#skF_10')=k2_lattices('#skF_9', B_153, '#skF_10') | ~m1_subset_1(B_153, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_91, c_1079])).
% 8.85/3.16  tff(c_1113, plain, (![B_155]: (k4_lattices('#skF_9', B_155, '#skF_10')=k2_lattices('#skF_9', B_155, '#skF_10') | ~m1_subset_1(B_155, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_86, c_1099])).
% 8.85/3.16  tff(c_1201, plain, (k4_lattices('#skF_9', '#skF_12', '#skF_10')=k2_lattices('#skF_9', '#skF_12', '#skF_10')), inference(resolution, [status(thm)], [c_74, c_1113])).
% 8.85/3.16  tff(c_1376, plain, (![A_156, C_157, B_158]: (k4_lattices(A_156, C_157, B_158)=k4_lattices(A_156, B_158, C_157) | ~m1_subset_1(C_157, u1_struct_0(A_156)) | ~m1_subset_1(B_158, u1_struct_0(A_156)) | ~l1_lattices(A_156) | ~v6_lattices(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.85/3.16  tff(c_1402, plain, (![B_158]: (k4_lattices('#skF_9', B_158, '#skF_10')=k4_lattices('#skF_9', '#skF_10', B_158) | ~m1_subset_1(B_158, u1_struct_0('#skF_9')) | ~l1_lattices('#skF_9') | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_78, c_1376])).
% 8.85/3.16  tff(c_1430, plain, (![B_158]: (k4_lattices('#skF_9', B_158, '#skF_10')=k4_lattices('#skF_9', '#skF_10', B_158) | ~m1_subset_1(B_158, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_91, c_1402])).
% 8.85/3.16  tff(c_2744, plain, (![B_177]: (k4_lattices('#skF_9', B_177, '#skF_10')=k4_lattices('#skF_9', '#skF_10', B_177) | ~m1_subset_1(B_177, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_86, c_1430])).
% 8.85/3.16  tff(c_2804, plain, (k4_lattices('#skF_9', '#skF_10', '#skF_12')=k4_lattices('#skF_9', '#skF_12', '#skF_10')), inference(resolution, [status(thm)], [c_74, c_2744])).
% 8.85/3.16  tff(c_2851, plain, (k2_lattices('#skF_9', '#skF_10', '#skF_12')=k2_lattices('#skF_9', '#skF_12', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_2264, c_1201, c_2804])).
% 8.85/3.16  tff(c_639, plain, (![A_143, B_144, C_145]: (k1_lattices(A_143, k2_lattices(A_143, B_144, C_145), C_145)=C_145 | ~m1_subset_1(C_145, u1_struct_0(A_143)) | ~m1_subset_1(B_144, u1_struct_0(A_143)) | ~v8_lattices(A_143) | ~l3_lattices(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_139])).
% 8.85/3.16  tff(c_665, plain, (![B_144]: (k1_lattices('#skF_9', k2_lattices('#skF_9', B_144, '#skF_12'), '#skF_12')='#skF_12' | ~m1_subset_1(B_144, u1_struct_0('#skF_9')) | ~v8_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_74, c_639])).
% 8.85/3.16  tff(c_689, plain, (![B_144]: (k1_lattices('#skF_9', k2_lattices('#skF_9', B_144, '#skF_12'), '#skF_12')='#skF_12' | ~m1_subset_1(B_144, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_196, c_665])).
% 8.85/3.16  tff(c_851, plain, (![B_150]: (k1_lattices('#skF_9', k2_lattices('#skF_9', B_150, '#skF_12'), '#skF_12')='#skF_12' | ~m1_subset_1(B_150, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_86, c_689])).
% 8.85/3.16  tff(c_937, plain, (k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_10', '#skF_12'), '#skF_12')='#skF_12'), inference(resolution, [status(thm)], [c_78, c_851])).
% 8.85/3.16  tff(c_2902, plain, (k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_12', '#skF_10'), '#skF_12')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2851, c_937])).
% 8.85/3.16  tff(c_2647, plain, (![C_175]: (k2_lattices('#skF_9', '#skF_12', k1_lattices('#skF_9', C_175, '#skF_12'))=k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_12', C_175), '#skF_12') | ~m1_subset_1('#skF_12', u1_struct_0('#skF_9')) | ~m1_subset_1(C_175, u1_struct_0('#skF_9')) | ~m1_subset_1('#skF_12', u1_struct_0('#skF_9')) | ~v11_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1840, c_2601])).
% 8.85/3.16  tff(c_2691, plain, (![C_175]: (k2_lattices('#skF_9', '#skF_12', k1_lattices('#skF_9', C_175, '#skF_12'))=k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_12', C_175), '#skF_12') | ~m1_subset_1(C_175, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_82, c_74, c_74, c_2647])).
% 8.85/3.16  tff(c_6969, plain, (![C_224]: (k2_lattices('#skF_9', '#skF_12', k1_lattices('#skF_9', C_224, '#skF_12'))=k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_12', C_224), '#skF_12') | ~m1_subset_1(C_224, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_86, c_2691])).
% 8.85/3.16  tff(c_7017, plain, (k2_lattices('#skF_9', '#skF_12', k1_lattices('#skF_9', '#skF_10', '#skF_12'))=k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_12', '#skF_10'), '#skF_12')), inference(resolution, [status(thm)], [c_78, c_6969])).
% 8.85/3.16  tff(c_7066, plain, (k1_lattices('#skF_9', '#skF_12', k2_lattices('#skF_9', '#skF_12', '#skF_10'))='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_5858, c_4310, c_2902, c_7017])).
% 8.85/3.16  tff(c_7072, plain, (k2_lattices('#skF_9', '#skF_12', k1_lattices('#skF_9', '#skF_12', '#skF_10'))='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_7066, c_5858])).
% 8.85/3.16  tff(c_70, plain, (k3_lattices('#skF_9', '#skF_10', '#skF_11')=k3_lattices('#skF_9', '#skF_10', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.85/3.16  tff(c_3749, plain, (k3_lattices('#skF_9', '#skF_10', '#skF_11')=k1_lattices('#skF_9', '#skF_10', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_3741, c_70])).
% 8.85/3.16  tff(c_821, plain, (![B_149]: (k3_lattices('#skF_9', B_149, '#skF_10')=k3_lattices('#skF_9', '#skF_10', B_149) | ~m1_subset_1(B_149, u1_struct_0('#skF_9')) | ~l2_lattices('#skF_9') | ~v4_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_78, c_799])).
% 8.85/3.16  tff(c_841, plain, (![B_149]: (k3_lattices('#skF_9', B_149, '#skF_10')=k3_lattices('#skF_9', '#skF_10', B_149) | ~m1_subset_1(B_149, u1_struct_0('#skF_9')) | ~v4_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_821])).
% 8.85/3.16  tff(c_842, plain, (![B_149]: (k3_lattices('#skF_9', B_149, '#skF_10')=k3_lattices('#skF_9', '#skF_10', B_149) | ~m1_subset_1(B_149, u1_struct_0('#skF_9')) | ~v4_lattices('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_86, c_841])).
% 8.85/3.16  tff(c_3883, plain, (![B_185]: (k3_lattices('#skF_9', B_185, '#skF_10')=k3_lattices('#skF_9', '#skF_10', B_185) | ~m1_subset_1(B_185, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_3647, c_842])).
% 8.85/3.16  tff(c_3931, plain, (k3_lattices('#skF_9', '#skF_11', '#skF_10')=k3_lattices('#skF_9', '#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_76, c_3883])).
% 8.85/3.16  tff(c_3976, plain, (k3_lattices('#skF_9', '#skF_11', '#skF_10')=k1_lattices('#skF_9', '#skF_10', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_3749, c_3931])).
% 8.85/3.16  tff(c_4262, plain, (k3_lattices('#skF_9', '#skF_11', '#skF_10')=k1_lattices('#skF_9', '#skF_11', '#skF_10')), inference(resolution, [status(thm)], [c_76, c_4214])).
% 8.85/3.16  tff(c_4308, plain, (k1_lattices('#skF_9', '#skF_11', '#skF_10')=k1_lattices('#skF_9', '#skF_10', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_3976, c_4262])).
% 8.85/3.16  tff(c_4325, plain, (k1_lattices('#skF_9', '#skF_11', '#skF_10')=k1_lattices('#skF_9', '#skF_12', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_4310, c_4308])).
% 8.85/3.16  tff(c_607, plain, (![B_141]: (k3_lattices('#skF_9', B_141, '#skF_11')=k1_lattices('#skF_9', B_141, '#skF_11') | ~m1_subset_1(B_141, u1_struct_0('#skF_9')) | ~l2_lattices('#skF_9') | ~v4_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_76, c_583])).
% 8.85/3.16  tff(c_629, plain, (![B_141]: (k3_lattices('#skF_9', B_141, '#skF_11')=k1_lattices('#skF_9', B_141, '#skF_11') | ~m1_subset_1(B_141, u1_struct_0('#skF_9')) | ~v4_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_607])).
% 8.85/3.16  tff(c_630, plain, (![B_141]: (k3_lattices('#skF_9', B_141, '#skF_11')=k1_lattices('#skF_9', B_141, '#skF_11') | ~m1_subset_1(B_141, u1_struct_0('#skF_9')) | ~v4_lattices('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_86, c_629])).
% 8.85/3.16  tff(c_3985, plain, (![B_186]: (k3_lattices('#skF_9', B_186, '#skF_11')=k1_lattices('#skF_9', B_186, '#skF_11') | ~m1_subset_1(B_186, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_3647, c_630])).
% 8.85/3.16  tff(c_4030, plain, (k3_lattices('#skF_9', '#skF_10', '#skF_11')=k1_lattices('#skF_9', '#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_78, c_3985])).
% 8.85/3.16  tff(c_4078, plain, (k1_lattices('#skF_9', '#skF_10', '#skF_11')=k1_lattices('#skF_9', '#skF_10', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_3749, c_4030])).
% 8.85/3.16  tff(c_4327, plain, (k1_lattices('#skF_9', '#skF_10', '#skF_11')=k1_lattices('#skF_9', '#skF_12', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_4310, c_4078])).
% 8.85/3.16  tff(c_1081, plain, (![B_153]: (k4_lattices('#skF_9', B_153, '#skF_11')=k2_lattices('#skF_9', B_153, '#skF_11') | ~m1_subset_1(B_153, u1_struct_0('#skF_9')) | ~l1_lattices('#skF_9') | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_76, c_1057])).
% 8.85/3.16  tff(c_1103, plain, (![B_153]: (k4_lattices('#skF_9', B_153, '#skF_11')=k2_lattices('#skF_9', B_153, '#skF_11') | ~m1_subset_1(B_153, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_91, c_1081])).
% 8.85/3.16  tff(c_1522, plain, (![B_159]: (k4_lattices('#skF_9', B_159, '#skF_11')=k2_lattices('#skF_9', B_159, '#skF_11') | ~m1_subset_1(B_159, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_86, c_1103])).
% 8.85/3.16  tff(c_1620, plain, (k4_lattices('#skF_9', '#skF_10', '#skF_11')=k2_lattices('#skF_9', '#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_78, c_1522])).
% 8.85/3.16  tff(c_72, plain, (k4_lattices('#skF_9', '#skF_10', '#skF_11')=k4_lattices('#skF_9', '#skF_10', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_244])).
% 8.85/3.16  tff(c_1623, plain, (k4_lattices('#skF_9', '#skF_10', '#skF_12')=k2_lattices('#skF_9', '#skF_10', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_72])).
% 8.85/3.16  tff(c_2348, plain, (k2_lattices('#skF_9', '#skF_10', '#skF_11')=k2_lattices('#skF_9', '#skF_10', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_2264, c_1623])).
% 8.85/3.16  tff(c_663, plain, (![B_144]: (k1_lattices('#skF_9', k2_lattices('#skF_9', B_144, '#skF_11'), '#skF_11')='#skF_11' | ~m1_subset_1(B_144, u1_struct_0('#skF_9')) | ~v8_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_76, c_639])).
% 8.85/3.16  tff(c_685, plain, (![B_144]: (k1_lattices('#skF_9', k2_lattices('#skF_9', B_144, '#skF_11'), '#skF_11')='#skF_11' | ~m1_subset_1(B_144, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_196, c_663])).
% 8.85/3.16  tff(c_956, plain, (![B_151]: (k1_lattices('#skF_9', k2_lattices('#skF_9', B_151, '#skF_11'), '#skF_11')='#skF_11' | ~m1_subset_1(B_151, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_86, c_685])).
% 8.85/3.16  tff(c_1042, plain, (k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_10', '#skF_11'), '#skF_11')='#skF_11'), inference(resolution, [status(thm)], [c_78, c_956])).
% 8.85/3.16  tff(c_2583, plain, (k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_10', '#skF_12'), '#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_2348, c_1042])).
% 8.85/3.16  tff(c_2895, plain, (k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_12', '#skF_10'), '#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_2851, c_2583])).
% 8.85/3.16  tff(c_2582, plain, (k4_lattices('#skF_9', '#skF_10', '#skF_11')=k2_lattices('#skF_9', '#skF_10', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_2348, c_1620])).
% 8.85/3.16  tff(c_1200, plain, (k4_lattices('#skF_9', '#skF_11', '#skF_10')=k2_lattices('#skF_9', '#skF_11', '#skF_10')), inference(resolution, [status(thm)], [c_76, c_1113])).
% 8.85/3.16  tff(c_2801, plain, (k4_lattices('#skF_9', '#skF_11', '#skF_10')=k4_lattices('#skF_9', '#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_76, c_2744])).
% 8.85/3.16  tff(c_2849, plain, (k2_lattices('#skF_9', '#skF_11', '#skF_10')=k2_lattices('#skF_9', '#skF_10', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_2582, c_1200, c_2801])).
% 8.85/3.16  tff(c_2891, plain, (k2_lattices('#skF_9', '#skF_11', '#skF_10')=k2_lattices('#skF_9', '#skF_12', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_2851, c_2849])).
% 8.85/3.16  tff(c_140, plain, (k1_lattices('#skF_9', '#skF_11', '#skF_11')='#skF_11' | ~l3_lattices('#skF_9') | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_76, c_120])).
% 8.85/3.16  tff(c_157, plain, (k1_lattices('#skF_9', '#skF_11', '#skF_11')='#skF_11' | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_140])).
% 8.85/3.16  tff(c_158, plain, (k1_lattices('#skF_9', '#skF_11', '#skF_11')='#skF_11' | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | ~v6_lattices('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_86, c_157])).
% 8.85/3.16  tff(c_257, plain, (k1_lattices('#skF_9', '#skF_11', '#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_196, c_184, c_158])).
% 8.85/3.16  tff(c_229, plain, (![B_132]: (r1_lattices('#skF_9', B_132, '#skF_11') | k1_lattices('#skF_9', B_132, '#skF_11')!='#skF_11' | ~m1_subset_1(B_132, u1_struct_0('#skF_9')) | ~l2_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_76, c_209])).
% 8.85/3.16  tff(c_246, plain, (![B_132]: (r1_lattices('#skF_9', B_132, '#skF_11') | k1_lattices('#skF_9', B_132, '#skF_11')!='#skF_11' | ~m1_subset_1(B_132, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_229])).
% 8.85/3.16  tff(c_485, plain, (![B_139]: (r1_lattices('#skF_9', B_139, '#skF_11') | k1_lattices('#skF_9', B_139, '#skF_11')!='#skF_11' | ~m1_subset_1(B_139, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_86, c_246])).
% 8.85/3.16  tff(c_530, plain, (r1_lattices('#skF_9', '#skF_11', '#skF_11') | k1_lattices('#skF_9', '#skF_11', '#skF_11')!='#skF_11'), inference(resolution, [status(thm)], [c_76, c_485])).
% 8.85/3.16  tff(c_574, plain, (r1_lattices('#skF_9', '#skF_11', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_530])).
% 8.85/3.16  tff(c_1812, plain, (k2_lattices('#skF_9', '#skF_11', '#skF_11')='#skF_11' | ~m1_subset_1('#skF_11', u1_struct_0('#skF_9')) | ~l3_lattices('#skF_9') | ~v9_lattices('#skF_9') | ~v8_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_574, c_1802])).
% 8.85/3.16  tff(c_1835, plain, (k2_lattices('#skF_9', '#skF_11', '#skF_11')='#skF_11' | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_184, c_80, c_76, c_1812])).
% 8.85/3.16  tff(c_1836, plain, (k2_lattices('#skF_9', '#skF_11', '#skF_11')='#skF_11'), inference(negUnitSimplification, [status(thm)], [c_86, c_1835])).
% 8.85/3.16  tff(c_2653, plain, (![C_175]: (k2_lattices('#skF_9', '#skF_11', k1_lattices('#skF_9', C_175, '#skF_11'))=k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_11', C_175), '#skF_11') | ~m1_subset_1('#skF_11', u1_struct_0('#skF_9')) | ~m1_subset_1(C_175, u1_struct_0('#skF_9')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_9')) | ~v11_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1836, c_2601])).
% 8.85/3.16  tff(c_2697, plain, (![C_175]: (k2_lattices('#skF_9', '#skF_11', k1_lattices('#skF_9', C_175, '#skF_11'))=k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_11', C_175), '#skF_11') | ~m1_subset_1(C_175, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_82, c_76, c_76, c_2653])).
% 8.85/3.16  tff(c_6825, plain, (![C_221]: (k2_lattices('#skF_9', '#skF_11', k1_lattices('#skF_9', C_221, '#skF_11'))=k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_11', C_221), '#skF_11') | ~m1_subset_1(C_221, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_86, c_2697])).
% 8.85/3.16  tff(c_6873, plain, (k2_lattices('#skF_9', '#skF_11', k1_lattices('#skF_9', '#skF_10', '#skF_11'))=k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_11', '#skF_10'), '#skF_11')), inference(resolution, [status(thm)], [c_78, c_6825])).
% 8.85/3.16  tff(c_6922, plain, (k2_lattices('#skF_9', '#skF_11', k1_lattices('#skF_9', '#skF_12', '#skF_10'))='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_4327, c_2895, c_2891, c_6873])).
% 8.85/3.16  tff(c_2265, plain, (k4_lattices('#skF_9', '#skF_11', '#skF_12')=k2_lattices('#skF_9', '#skF_11', '#skF_12')), inference(resolution, [status(thm)], [c_76, c_2166])).
% 8.85/3.16  tff(c_1622, plain, (k4_lattices('#skF_9', '#skF_12', '#skF_11')=k2_lattices('#skF_9', '#skF_12', '#skF_11')), inference(resolution, [status(thm)], [c_74, c_1522])).
% 8.85/3.16  tff(c_1404, plain, (![B_158]: (k4_lattices('#skF_9', B_158, '#skF_11')=k4_lattices('#skF_9', '#skF_11', B_158) | ~m1_subset_1(B_158, u1_struct_0('#skF_9')) | ~l1_lattices('#skF_9') | ~v6_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_76, c_1376])).
% 8.85/3.16  tff(c_1434, plain, (![B_158]: (k4_lattices('#skF_9', B_158, '#skF_11')=k4_lattices('#skF_9', '#skF_11', B_158) | ~m1_subset_1(B_158, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_91, c_1404])).
% 8.85/3.16  tff(c_2964, plain, (![B_178]: (k4_lattices('#skF_9', B_178, '#skF_11')=k4_lattices('#skF_9', '#skF_11', B_178) | ~m1_subset_1(B_178, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_86, c_1434])).
% 8.85/3.16  tff(c_3018, plain, (k4_lattices('#skF_9', '#skF_11', '#skF_12')=k4_lattices('#skF_9', '#skF_12', '#skF_11')), inference(resolution, [status(thm)], [c_74, c_2964])).
% 8.85/3.16  tff(c_3063, plain, (k2_lattices('#skF_9', '#skF_11', '#skF_12')=k2_lattices('#skF_9', '#skF_12', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_2265, c_1622, c_3018])).
% 8.85/3.16  tff(c_20, plain, (![A_8, B_23, C_27, D_29]: (k1_lattices(A_8, k2_lattices(A_8, B_23, C_27), k2_lattices(A_8, B_23, D_29))=k2_lattices(A_8, B_23, k1_lattices(A_8, C_27, D_29)) | ~m1_subset_1(D_29, u1_struct_0(A_8)) | ~m1_subset_1(C_27, u1_struct_0(A_8)) | ~m1_subset_1(B_23, u1_struct_0(A_8)) | ~v11_lattices(A_8) | ~l3_lattices(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.85/3.16  tff(c_2868, plain, (![C_27]: (k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_11', C_27), k2_lattices('#skF_9', '#skF_10', '#skF_12'))=k2_lattices('#skF_9', '#skF_11', k1_lattices('#skF_9', C_27, '#skF_10')) | ~m1_subset_1('#skF_10', u1_struct_0('#skF_9')) | ~m1_subset_1(C_27, u1_struct_0('#skF_9')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_9')) | ~v11_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2849, c_20])).
% 8.85/3.16  tff(c_2875, plain, (![C_27]: (k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_11', C_27), k2_lattices('#skF_9', '#skF_10', '#skF_12'))=k2_lattices('#skF_9', '#skF_11', k1_lattices('#skF_9', C_27, '#skF_10')) | ~m1_subset_1(C_27, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_82, c_76, c_78, c_2868])).
% 8.85/3.16  tff(c_2876, plain, (![C_27]: (k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_11', C_27), k2_lattices('#skF_9', '#skF_10', '#skF_12'))=k2_lattices('#skF_9', '#skF_11', k1_lattices('#skF_9', C_27, '#skF_10')) | ~m1_subset_1(C_27, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_86, c_2875])).
% 8.85/3.16  tff(c_10409, plain, (![C_276]: (k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_11', C_276), k2_lattices('#skF_9', '#skF_12', '#skF_10'))=k2_lattices('#skF_9', '#skF_11', k1_lattices('#skF_9', C_276, '#skF_10')) | ~m1_subset_1(C_276, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_2851, c_2876])).
% 8.85/3.16  tff(c_10441, plain, (k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_12', '#skF_11'), k2_lattices('#skF_9', '#skF_12', '#skF_10'))=k2_lattices('#skF_9', '#skF_11', k1_lattices('#skF_9', '#skF_12', '#skF_10')) | ~m1_subset_1('#skF_12', u1_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3063, c_10409])).
% 8.85/3.16  tff(c_10460, plain, (k1_lattices('#skF_9', k2_lattices('#skF_9', '#skF_12', '#skF_11'), k2_lattices('#skF_9', '#skF_12', '#skF_10'))='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6922, c_10441])).
% 8.85/3.16  tff(c_10468, plain, (k2_lattices('#skF_9', '#skF_12', k1_lattices('#skF_9', '#skF_11', '#skF_10'))='#skF_11' | ~m1_subset_1('#skF_10', u1_struct_0('#skF_9')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_9')) | ~m1_subset_1('#skF_12', u1_struct_0('#skF_9')) | ~v11_lattices('#skF_9') | ~l3_lattices('#skF_9') | v2_struct_0('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_10460, c_20])).
% 8.85/3.16  tff(c_10475, plain, ('#skF_11'='#skF_12' | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_82, c_74, c_76, c_78, c_7072, c_4325, c_10468])).
% 8.85/3.16  tff(c_10477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_68, c_10475])).
% 8.85/3.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.85/3.16  
% 8.85/3.16  Inference rules
% 8.85/3.16  ----------------------
% 8.85/3.16  #Ref     : 0
% 8.85/3.16  #Sup     : 2082
% 8.85/3.16  #Fact    : 0
% 8.85/3.16  #Define  : 0
% 8.85/3.16  #Split   : 22
% 8.85/3.16  #Chain   : 0
% 8.85/3.16  #Close   : 0
% 8.85/3.16  
% 8.85/3.16  Ordering : KBO
% 8.85/3.16  
% 8.85/3.16  Simplification rules
% 8.85/3.16  ----------------------
% 8.85/3.16  #Subsume      : 43
% 8.85/3.16  #Demod        : 3298
% 8.85/3.16  #Tautology    : 1192
% 8.85/3.16  #SimpNegUnit  : 822
% 8.85/3.16  #BackRed      : 100
% 8.85/3.16  
% 8.85/3.16  #Partial instantiations: 0
% 8.85/3.16  #Strategies tried      : 1
% 8.85/3.16  
% 8.85/3.16  Timing (in seconds)
% 8.85/3.16  ----------------------
% 8.85/3.16  Preprocessing        : 0.40
% 8.85/3.16  Parsing              : 0.20
% 8.85/3.16  CNF conversion       : 0.04
% 8.85/3.16  Main loop            : 1.94
% 8.85/3.16  Inferencing          : 0.50
% 8.85/3.16  Reduction            : 0.85
% 8.85/3.16  Demodulation         : 0.64
% 8.85/3.16  BG Simplification    : 0.07
% 8.85/3.16  Subsumption          : 0.40
% 8.85/3.16  Abstraction          : 0.10
% 8.85/3.16  MUC search           : 0.00
% 8.85/3.16  Cooper               : 0.00
% 8.85/3.16  Total                : 2.42
% 8.85/3.16  Index Insertion      : 0.00
% 8.85/3.16  Index Deletion       : 0.00
% 8.85/3.16  Index Matching       : 0.00
% 8.85/3.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
