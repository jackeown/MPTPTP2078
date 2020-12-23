%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:14 EST 2020

% Result     : Theorem 4.52s
% Output     : CNFRefutation 4.97s
% Verified   : 
% Statistics : Number of formulae       :  183 (1037 expanded)
%              Number of leaves         :   43 ( 370 expanded)
%              Depth                    :   19
%              Number of atoms          :  423 (4671 expanded)
%              Number of equality atoms :  114 (1123 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v11_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > k2_zfmisc_1 > #nlpp > u1_struct_0 > #skF_7 > #skF_5 > #skF_2 > #skF_4 > #skF_11 > #skF_1 > #skF_10 > #skF_9 > #skF_8 > #skF_3 > #skF_6

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_185,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_lattices)).

tff(f_51,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_160,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k1_lattices(A,B,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattices)).

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v8_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k1_lattices(A,k2_lattices(A,B,C),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

tff(f_118,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_144,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k4_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v9_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,k1_lattices(A,B,C)) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

tff(f_82,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_lattices)).

tff(f_131,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(c_56,plain,(
    '#skF_11' != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_62,plain,(
    m1_subset_1('#skF_11',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_66,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_68,plain,(
    l3_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_72,plain,(
    v10_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_6,plain,(
    ! [A_3] :
      ( v8_lattices(A_3)
      | ~ v10_lattices(A_3)
      | v2_struct_0(A_3)
      | ~ l3_lattices(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_3] :
      ( v9_lattices(A_3)
      | ~ v10_lattices(A_3)
      | v2_struct_0(A_3)
      | ~ l3_lattices(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_3] :
      ( v6_lattices(A_3)
      | ~ v10_lattices(A_3)
      | v2_struct_0(A_3)
      | ~ l3_lattices(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_64,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_113,plain,(
    ! [A_95,B_96] :
      ( k1_lattices(A_95,B_96,B_96) = B_96
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l3_lattices(A_95)
      | ~ v9_lattices(A_95)
      | ~ v8_lattices(A_95)
      | ~ v6_lattices(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_129,plain,
    ( k1_lattices('#skF_8','#skF_10','#skF_10') = '#skF_10'
    | ~ l3_lattices('#skF_8')
    | ~ v9_lattices('#skF_8')
    | ~ v8_lattices('#skF_8')
    | ~ v6_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_113])).

tff(c_143,plain,
    ( k1_lattices('#skF_8','#skF_10','#skF_10') = '#skF_10'
    | ~ v9_lattices('#skF_8')
    | ~ v8_lattices('#skF_8')
    | ~ v6_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_129])).

tff(c_144,plain,
    ( k1_lattices('#skF_8','#skF_10','#skF_10') = '#skF_10'
    | ~ v9_lattices('#skF_8')
    | ~ v8_lattices('#skF_8')
    | ~ v6_lattices('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_143])).

tff(c_153,plain,(
    ~ v6_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_156,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_10,c_153])).

tff(c_159,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_156])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_159])).

tff(c_162,plain,
    ( ~ v8_lattices('#skF_8')
    | ~ v9_lattices('#skF_8')
    | k1_lattices('#skF_8','#skF_10','#skF_10') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_164,plain,(
    ~ v9_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_207,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_164])).

tff(c_210,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_207])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_210])).

tff(c_213,plain,
    ( ~ v8_lattices('#skF_8')
    | k1_lattices('#skF_8','#skF_10','#skF_10') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_215,plain,(
    ~ v8_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_221,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_215])).

tff(c_224,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_221])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_224])).

tff(c_228,plain,(
    v8_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_245,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_lattices(A_100,k2_lattices(A_100,B_101,C_102),C_102) = C_102
      | ~ m1_subset_1(C_102,u1_struct_0(A_100))
      | ~ m1_subset_1(B_101,u1_struct_0(A_100))
      | ~ v8_lattices(A_100)
      | ~ l3_lattices(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_261,plain,(
    ! [B_101] :
      ( k1_lattices('#skF_8',k2_lattices('#skF_8',B_101,'#skF_10'),'#skF_10') = '#skF_10'
      | ~ m1_subset_1(B_101,u1_struct_0('#skF_8'))
      | ~ v8_lattices('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_64,c_245])).

tff(c_275,plain,(
    ! [B_101] :
      ( k1_lattices('#skF_8',k2_lattices('#skF_8',B_101,'#skF_10'),'#skF_10') = '#skF_10'
      | ~ m1_subset_1(B_101,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_228,c_261])).

tff(c_285,plain,(
    ! [B_103] :
      ( k1_lattices('#skF_8',k2_lattices('#skF_8',B_103,'#skF_10'),'#skF_10') = '#skF_10'
      | ~ m1_subset_1(B_103,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_275])).

tff(c_353,plain,(
    k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_10'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_66,c_285])).

tff(c_163,plain,(
    v6_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_80,plain,(
    ! [A_77] :
      ( l1_lattices(A_77)
      | ~ l3_lattices(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_84,plain,(
    l1_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_80])).

tff(c_516,plain,(
    ! [A_106,B_107,C_108] :
      ( k4_lattices(A_106,B_107,C_108) = k2_lattices(A_106,B_107,C_108)
      | ~ m1_subset_1(C_108,u1_struct_0(A_106))
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ l1_lattices(A_106)
      | ~ v6_lattices(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_536,plain,(
    ! [B_107] :
      ( k4_lattices('#skF_8',B_107,'#skF_9') = k2_lattices('#skF_8',B_107,'#skF_9')
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_8'))
      | ~ l1_lattices('#skF_8')
      | ~ v6_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_66,c_516])).

tff(c_554,plain,(
    ! [B_107] :
      ( k4_lattices('#skF_8',B_107,'#skF_9') = k2_lattices('#skF_8',B_107,'#skF_9')
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_84,c_536])).

tff(c_654,plain,(
    ! [B_110] :
      ( k4_lattices('#skF_8',B_110,'#skF_9') = k2_lattices('#skF_8',B_110,'#skF_9')
      | ~ m1_subset_1(B_110,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_554])).

tff(c_720,plain,(
    k4_lattices('#skF_8','#skF_10','#skF_9') = k2_lattices('#skF_8','#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_654])).

tff(c_532,plain,(
    ! [B_107] :
      ( k4_lattices('#skF_8',B_107,'#skF_10') = k2_lattices('#skF_8',B_107,'#skF_10')
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_8'))
      | ~ l1_lattices('#skF_8')
      | ~ v6_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_64,c_516])).

tff(c_546,plain,(
    ! [B_107] :
      ( k4_lattices('#skF_8',B_107,'#skF_10') = k2_lattices('#skF_8',B_107,'#skF_10')
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_84,c_532])).

tff(c_568,plain,(
    ! [B_109] :
      ( k4_lattices('#skF_8',B_109,'#skF_10') = k2_lattices('#skF_8',B_109,'#skF_10')
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_546])).

tff(c_636,plain,(
    k4_lattices('#skF_8','#skF_9','#skF_10') = k2_lattices('#skF_8','#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_568])).

tff(c_1060,plain,(
    ! [A_120,C_121,B_122] :
      ( k4_lattices(A_120,C_121,B_122) = k4_lattices(A_120,B_122,C_121)
      | ~ m1_subset_1(C_121,u1_struct_0(A_120))
      | ~ m1_subset_1(B_122,u1_struct_0(A_120))
      | ~ l1_lattices(A_120)
      | ~ v6_lattices(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1076,plain,(
    ! [B_122] :
      ( k4_lattices('#skF_8',B_122,'#skF_10') = k4_lattices('#skF_8','#skF_10',B_122)
      | ~ m1_subset_1(B_122,u1_struct_0('#skF_8'))
      | ~ l1_lattices('#skF_8')
      | ~ v6_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_64,c_1060])).

tff(c_1090,plain,(
    ! [B_122] :
      ( k4_lattices('#skF_8',B_122,'#skF_10') = k4_lattices('#skF_8','#skF_10',B_122)
      | ~ m1_subset_1(B_122,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_84,c_1076])).

tff(c_1179,plain,(
    ! [B_124] :
      ( k4_lattices('#skF_8',B_124,'#skF_10') = k4_lattices('#skF_8','#skF_10',B_124)
      | ~ m1_subset_1(B_124,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1090])).

tff(c_1216,plain,(
    k4_lattices('#skF_8','#skF_10','#skF_9') = k4_lattices('#skF_8','#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_1179])).

tff(c_1250,plain,(
    k2_lattices('#skF_8','#skF_10','#skF_9') = k2_lattices('#skF_8','#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_720,c_636,c_1216])).

tff(c_70,plain,(
    v11_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_227,plain,(
    k1_lattices('#skF_8','#skF_10','#skF_10') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_214,plain,(
    v9_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_723,plain,(
    ! [A_111,B_112,C_113] :
      ( k2_lattices(A_111,B_112,k1_lattices(A_111,B_112,C_113)) = B_112
      | ~ m1_subset_1(C_113,u1_struct_0(A_111))
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ v9_lattices(A_111)
      | ~ l3_lattices(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_739,plain,(
    ! [B_112] :
      ( k2_lattices('#skF_8',B_112,k1_lattices('#skF_8',B_112,'#skF_10')) = B_112
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_8'))
      | ~ v9_lattices('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_64,c_723])).

tff(c_753,plain,(
    ! [B_112] :
      ( k2_lattices('#skF_8',B_112,k1_lattices('#skF_8',B_112,'#skF_10')) = B_112
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_214,c_739])).

tff(c_862,plain,(
    ! [B_115] :
      ( k2_lattices('#skF_8',B_115,k1_lattices('#skF_8',B_115,'#skF_10')) = B_115
      | ~ m1_subset_1(B_115,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_753])).

tff(c_885,plain,(
    k2_lattices('#skF_8','#skF_10',k1_lattices('#skF_8','#skF_10','#skF_10')) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_64,c_862])).

tff(c_919,plain,(
    k2_lattices('#skF_8','#skF_10','#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_885])).

tff(c_1446,plain,(
    ! [A_128,B_129,C_130,D_131] :
      ( k1_lattices(A_128,k2_lattices(A_128,B_129,C_130),k2_lattices(A_128,B_129,D_131)) = k2_lattices(A_128,B_129,k1_lattices(A_128,C_130,D_131))
      | ~ m1_subset_1(D_131,u1_struct_0(A_128))
      | ~ m1_subset_1(C_130,u1_struct_0(A_128))
      | ~ m1_subset_1(B_129,u1_struct_0(A_128))
      | ~ v11_lattices(A_128)
      | ~ l3_lattices(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1528,plain,(
    ! [C_130] :
      ( k2_lattices('#skF_8','#skF_10',k1_lattices('#skF_8',C_130,'#skF_10')) = k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_10',C_130),'#skF_10')
      | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_8'))
      | ~ m1_subset_1(C_130,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_8'))
      | ~ v11_lattices('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_919,c_1446])).

tff(c_1608,plain,(
    ! [C_130] :
      ( k2_lattices('#skF_8','#skF_10',k1_lattices('#skF_8',C_130,'#skF_10')) = k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_10',C_130),'#skF_10')
      | ~ m1_subset_1(C_130,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_64,c_64,c_1528])).

tff(c_1955,plain,(
    ! [C_136] :
      ( k2_lattices('#skF_8','#skF_10',k1_lattices('#skF_8',C_136,'#skF_10')) = k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_10',C_136),'#skF_10')
      | ~ m1_subset_1(C_136,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1608])).

tff(c_1992,plain,(
    k2_lattices('#skF_8','#skF_10',k1_lattices('#skF_8','#skF_9','#skF_10')) = k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_10','#skF_9'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_1955])).

tff(c_2026,plain,(
    k2_lattices('#skF_8','#skF_10',k1_lattices('#skF_8','#skF_9','#skF_10')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_1250,c_1992])).

tff(c_14,plain,(
    ! [A_3] :
      ( v4_lattices(A_3)
      | ~ v10_lattices(A_3)
      | v2_struct_0(A_3)
      | ~ l3_lattices(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_75,plain,(
    ! [A_76] :
      ( l2_lattices(A_76)
      | ~ l3_lattices(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_79,plain,(
    l2_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_75])).

tff(c_922,plain,(
    ! [A_116,B_117,C_118] :
      ( k3_lattices(A_116,B_117,C_118) = k1_lattices(A_116,B_117,C_118)
      | ~ m1_subset_1(C_118,u1_struct_0(A_116))
      | ~ m1_subset_1(B_117,u1_struct_0(A_116))
      | ~ l2_lattices(A_116)
      | ~ v4_lattices(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_942,plain,(
    ! [B_117] :
      ( k3_lattices('#skF_8',B_117,'#skF_9') = k1_lattices('#skF_8',B_117,'#skF_9')
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_8'))
      | ~ l2_lattices('#skF_8')
      | ~ v4_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_66,c_922])).

tff(c_960,plain,(
    ! [B_117] :
      ( k3_lattices('#skF_8',B_117,'#skF_9') = k1_lattices('#skF_8',B_117,'#skF_9')
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_8'))
      | ~ v4_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_942])).

tff(c_961,plain,(
    ! [B_117] :
      ( k3_lattices('#skF_8',B_117,'#skF_9') = k1_lattices('#skF_8',B_117,'#skF_9')
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_8'))
      | ~ v4_lattices('#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_960])).

tff(c_1435,plain,(
    ~ v4_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_961])).

tff(c_1438,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_14,c_1435])).

tff(c_1441,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_72,c_1438])).

tff(c_1443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1441])).

tff(c_1445,plain,(
    v4_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_961])).

tff(c_938,plain,(
    ! [B_117] :
      ( k3_lattices('#skF_8',B_117,'#skF_10') = k1_lattices('#skF_8',B_117,'#skF_10')
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_8'))
      | ~ l2_lattices('#skF_8')
      | ~ v4_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_64,c_922])).

tff(c_952,plain,(
    ! [B_117] :
      ( k3_lattices('#skF_8',B_117,'#skF_10') = k1_lattices('#skF_8',B_117,'#skF_10')
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_8'))
      | ~ v4_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_938])).

tff(c_953,plain,(
    ! [B_117] :
      ( k3_lattices('#skF_8',B_117,'#skF_10') = k1_lattices('#skF_8',B_117,'#skF_10')
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_8'))
      | ~ v4_lattices('#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_952])).

tff(c_1700,plain,(
    ! [B_133] :
      ( k3_lattices('#skF_8',B_133,'#skF_10') = k1_lattices('#skF_8',B_133,'#skF_10')
      | ~ m1_subset_1(B_133,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1445,c_953])).

tff(c_1769,plain,(
    k3_lattices('#skF_8','#skF_9','#skF_10') = k1_lattices('#skF_8','#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_1700])).

tff(c_58,plain,(
    k3_lattices('#skF_8','#skF_9','#skF_11') = k3_lattices('#skF_8','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_1774,plain,(
    k3_lattices('#skF_8','#skF_9','#skF_11') = k1_lattices('#skF_8','#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1769,c_58])).

tff(c_940,plain,(
    ! [B_117] :
      ( k3_lattices('#skF_8',B_117,'#skF_11') = k1_lattices('#skF_8',B_117,'#skF_11')
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_8'))
      | ~ l2_lattices('#skF_8')
      | ~ v4_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_62,c_922])).

tff(c_956,plain,(
    ! [B_117] :
      ( k3_lattices('#skF_8',B_117,'#skF_11') = k1_lattices('#skF_8',B_117,'#skF_11')
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_8'))
      | ~ v4_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_940])).

tff(c_957,plain,(
    ! [B_117] :
      ( k3_lattices('#skF_8',B_117,'#skF_11') = k1_lattices('#skF_8',B_117,'#skF_11')
      | ~ m1_subset_1(B_117,u1_struct_0('#skF_8'))
      | ~ v4_lattices('#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_956])).

tff(c_1785,plain,(
    ! [B_134] :
      ( k3_lattices('#skF_8',B_134,'#skF_11') = k1_lattices('#skF_8',B_134,'#skF_11')
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1445,c_957])).

tff(c_1854,plain,(
    k3_lattices('#skF_8','#skF_9','#skF_11') = k1_lattices('#skF_8','#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_66,c_1785])).

tff(c_1863,plain,(
    k1_lattices('#skF_8','#skF_9','#skF_11') = k1_lattices('#skF_8','#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1774,c_1854])).

tff(c_1465,plain,(
    ! [D_131] :
      ( k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_10'),k2_lattices('#skF_8','#skF_10',D_131)) = k2_lattices('#skF_8','#skF_10',k1_lattices('#skF_8','#skF_9',D_131))
      | ~ m1_subset_1(D_131,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_8'))
      | ~ v11_lattices('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1250,c_1446])).

tff(c_1545,plain,(
    ! [D_131] :
      ( k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_10'),k2_lattices('#skF_8','#skF_10',D_131)) = k2_lattices('#skF_8','#skF_10',k1_lattices('#skF_8','#skF_9',D_131))
      | ~ m1_subset_1(D_131,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_64,c_66,c_1465])).

tff(c_3065,plain,(
    ! [D_161] :
      ( k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_10'),k2_lattices('#skF_8','#skF_10',D_161)) = k2_lattices('#skF_8','#skF_10',k1_lattices('#skF_8','#skF_9',D_161))
      | ~ m1_subset_1(D_161,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1545])).

tff(c_60,plain,(
    k4_lattices('#skF_8','#skF_9','#skF_11') = k4_lattices('#skF_8','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_645,plain,(
    k4_lattices('#skF_8','#skF_9','#skF_11') = k2_lattices('#skF_8','#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_60])).

tff(c_534,plain,(
    ! [B_107] :
      ( k4_lattices('#skF_8',B_107,'#skF_11') = k2_lattices('#skF_8',B_107,'#skF_11')
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_8'))
      | ~ l1_lattices('#skF_8')
      | ~ v6_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_62,c_516])).

tff(c_550,plain,(
    ! [B_107] :
      ( k4_lattices('#skF_8',B_107,'#skF_11') = k2_lattices('#skF_8',B_107,'#skF_11')
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_84,c_534])).

tff(c_775,plain,(
    ! [B_114] :
      ( k4_lattices('#skF_8',B_114,'#skF_11') = k2_lattices('#skF_8',B_114,'#skF_11')
      | ~ m1_subset_1(B_114,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_550])).

tff(c_812,plain,(
    k4_lattices('#skF_8','#skF_9','#skF_11') = k2_lattices('#skF_8','#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_66,c_775])).

tff(c_844,plain,(
    k2_lattices('#skF_8','#skF_9','#skF_11') = k2_lattices('#skF_8','#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_812])).

tff(c_263,plain,(
    ! [B_101] :
      ( k1_lattices('#skF_8',k2_lattices('#skF_8',B_101,'#skF_11'),'#skF_11') = '#skF_11'
      | ~ m1_subset_1(B_101,u1_struct_0('#skF_8'))
      | ~ v8_lattices('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_62,c_245])).

tff(c_279,plain,(
    ! [B_101] :
      ( k1_lattices('#skF_8',k2_lattices('#skF_8',B_101,'#skF_11'),'#skF_11') = '#skF_11'
      | ~ m1_subset_1(B_101,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_228,c_263])).

tff(c_366,plain,(
    ! [B_104] :
      ( k1_lattices('#skF_8',k2_lattices('#skF_8',B_104,'#skF_11'),'#skF_11') = '#skF_11'
      | ~ m1_subset_1(B_104,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_279])).

tff(c_434,plain,(
    k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_11'),'#skF_11') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_66,c_366])).

tff(c_853,plain,(
    k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_10'),'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_434])).

tff(c_721,plain,(
    k4_lattices('#skF_8','#skF_11','#skF_9') = k2_lattices('#skF_8','#skF_11','#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_654])).

tff(c_1080,plain,(
    ! [B_122] :
      ( k4_lattices('#skF_8',B_122,'#skF_9') = k4_lattices('#skF_8','#skF_9',B_122)
      | ~ m1_subset_1(B_122,u1_struct_0('#skF_8'))
      | ~ l1_lattices('#skF_8')
      | ~ v6_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_66,c_1060])).

tff(c_1098,plain,(
    ! [B_122] :
      ( k4_lattices('#skF_8',B_122,'#skF_9') = k4_lattices('#skF_8','#skF_9',B_122)
      | ~ m1_subset_1(B_122,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_84,c_1080])).

tff(c_1280,plain,(
    ! [B_126] :
      ( k4_lattices('#skF_8',B_126,'#skF_9') = k4_lattices('#skF_8','#skF_9',B_126)
      | ~ m1_subset_1(B_126,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1098])).

tff(c_1314,plain,(
    k4_lattices('#skF_8','#skF_11','#skF_9') = k4_lattices('#skF_8','#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_62,c_1280])).

tff(c_1349,plain,(
    k2_lattices('#skF_8','#skF_11','#skF_9') = k2_lattices('#skF_8','#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_645,c_1314])).

tff(c_131,plain,
    ( k1_lattices('#skF_8','#skF_11','#skF_11') = '#skF_11'
    | ~ l3_lattices('#skF_8')
    | ~ v9_lattices('#skF_8')
    | ~ v8_lattices('#skF_8')
    | ~ v6_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_113])).

tff(c_147,plain,
    ( k1_lattices('#skF_8','#skF_11','#skF_11') = '#skF_11'
    | ~ v9_lattices('#skF_8')
    | ~ v8_lattices('#skF_8')
    | ~ v6_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_131])).

tff(c_148,plain,
    ( k1_lattices('#skF_8','#skF_11','#skF_11') = '#skF_11'
    | ~ v9_lattices('#skF_8')
    | ~ v8_lattices('#skF_8')
    | ~ v6_lattices('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_147])).

tff(c_240,plain,(
    k1_lattices('#skF_8','#skF_11','#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_228,c_214,c_148])).

tff(c_741,plain,(
    ! [B_112] :
      ( k2_lattices('#skF_8',B_112,k1_lattices('#skF_8',B_112,'#skF_11')) = B_112
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_8'))
      | ~ v9_lattices('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_62,c_723])).

tff(c_757,plain,(
    ! [B_112] :
      ( k2_lattices('#skF_8',B_112,k1_lattices('#skF_8',B_112,'#skF_11')) = B_112
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_214,c_741])).

tff(c_981,plain,(
    ! [B_119] :
      ( k2_lattices('#skF_8',B_119,k1_lattices('#skF_8',B_119,'#skF_11')) = B_119
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_757])).

tff(c_1006,plain,(
    k2_lattices('#skF_8','#skF_11',k1_lattices('#skF_8','#skF_11','#skF_11')) = '#skF_11' ),
    inference(resolution,[status(thm)],[c_62,c_981])).

tff(c_1039,plain,(
    k2_lattices('#skF_8','#skF_11','#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_1006])).

tff(c_1510,plain,(
    ! [C_130] :
      ( k2_lattices('#skF_8','#skF_11',k1_lattices('#skF_8',C_130,'#skF_11')) = k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_11',C_130),'#skF_11')
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_8'))
      | ~ m1_subset_1(C_130,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_8'))
      | ~ v11_lattices('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1039,c_1446])).

tff(c_1590,plain,(
    ! [C_130] :
      ( k2_lattices('#skF_8','#skF_11',k1_lattices('#skF_8',C_130,'#skF_11')) = k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_11',C_130),'#skF_11')
      | ~ m1_subset_1(C_130,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_62,c_62,c_1510])).

tff(c_2341,plain,(
    ! [C_142] :
      ( k2_lattices('#skF_8','#skF_11',k1_lattices('#skF_8',C_142,'#skF_11')) = k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_11',C_142),'#skF_11')
      | ~ m1_subset_1(C_142,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1590])).

tff(c_2378,plain,(
    k2_lattices('#skF_8','#skF_11',k1_lattices('#skF_8','#skF_9','#skF_11')) = k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_11','#skF_9'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_66,c_2341])).

tff(c_2412,plain,(
    k2_lattices('#skF_8','#skF_11',k1_lattices('#skF_8','#skF_9','#skF_10')) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_853,c_1349,c_2378])).

tff(c_841,plain,(
    k4_lattices('#skF_8','#skF_10','#skF_11') = k2_lattices('#skF_8','#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_64,c_775])).

tff(c_635,plain,(
    k4_lattices('#skF_8','#skF_11','#skF_10') = k2_lattices('#skF_8','#skF_11','#skF_10') ),
    inference(resolution,[status(thm)],[c_62,c_568])).

tff(c_1213,plain,(
    k4_lattices('#skF_8','#skF_11','#skF_10') = k4_lattices('#skF_8','#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_62,c_1179])).

tff(c_1248,plain,(
    k2_lattices('#skF_8','#skF_11','#skF_10') = k2_lattices('#skF_8','#skF_10','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_635,c_1213])).

tff(c_1474,plain,(
    ! [C_130] :
      ( k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_11',C_130),k2_lattices('#skF_8','#skF_10','#skF_11')) = k2_lattices('#skF_8','#skF_11',k1_lattices('#skF_8',C_130,'#skF_10'))
      | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_8'))
      | ~ m1_subset_1(C_130,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_8'))
      | ~ v11_lattices('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1248,c_1446])).

tff(c_1554,plain,(
    ! [C_130] :
      ( k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_11',C_130),k2_lattices('#skF_8','#skF_10','#skF_11')) = k2_lattices('#skF_8','#skF_11',k1_lattices('#skF_8',C_130,'#skF_10'))
      | ~ m1_subset_1(C_130,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_62,c_64,c_1474])).

tff(c_2413,plain,(
    ! [C_143] :
      ( k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_11',C_143),k2_lattices('#skF_8','#skF_10','#skF_11')) = k2_lattices('#skF_8','#skF_11',k1_lattices('#skF_8',C_143,'#skF_10'))
      | ~ m1_subset_1(C_143,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1554])).

tff(c_2422,plain,
    ( k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_10'),k2_lattices('#skF_8','#skF_10','#skF_11')) = k2_lattices('#skF_8','#skF_11',k1_lattices('#skF_8','#skF_9','#skF_10'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_2413])).

tff(c_2438,plain,(
    k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_10'),k2_lattices('#skF_8','#skF_10','#skF_11')) = k2_lattices('#skF_8','#skF_11',k1_lattices('#skF_8','#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2422])).

tff(c_2501,plain,(
    k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_10'),k2_lattices('#skF_8','#skF_10','#skF_11')) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2412,c_2438])).

tff(c_3071,plain,
    ( k2_lattices('#skF_8','#skF_10',k1_lattices('#skF_8','#skF_9','#skF_11')) = '#skF_11'
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3065,c_2501])).

tff(c_3118,plain,(
    '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2026,c_1863,c_3071])).

tff(c_3120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 19:55:04 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.52/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.86  
% 4.52/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.87  %$ m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v11_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > k2_zfmisc_1 > #nlpp > u1_struct_0 > #skF_7 > #skF_5 > #skF_2 > #skF_4 > #skF_11 > #skF_1 > #skF_10 > #skF_9 > #skF_8 > #skF_3 > #skF_6
% 4.52/1.87  
% 4.52/1.87  %Foreground sorts:
% 4.52/1.87  
% 4.52/1.87  
% 4.52/1.87  %Background operators:
% 4.52/1.87  
% 4.52/1.87  
% 4.52/1.87  %Foreground operators:
% 4.52/1.87  tff(l3_lattices, type, l3_lattices: $i > $o).
% 4.52/1.87  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 4.52/1.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.52/1.87  tff('#skF_7', type, '#skF_7': $i > $i).
% 4.52/1.87  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 4.52/1.87  tff('#skF_5', type, '#skF_5': $i > $i).
% 4.52/1.87  tff(l2_lattices, type, l2_lattices: $i > $o).
% 4.52/1.87  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.52/1.87  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.52/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.52/1.87  tff('#skF_11', type, '#skF_11': $i).
% 4.52/1.87  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 4.52/1.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.52/1.87  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 4.52/1.87  tff(l1_lattices, type, l1_lattices: $i > $o).
% 4.52/1.87  tff('#skF_10', type, '#skF_10': $i).
% 4.52/1.87  tff(v4_lattices, type, v4_lattices: $i > $o).
% 4.52/1.87  tff(v6_lattices, type, v6_lattices: $i > $o).
% 4.52/1.87  tff(v9_lattices, type, v9_lattices: $i > $o).
% 4.52/1.87  tff(v5_lattices, type, v5_lattices: $i > $o).
% 4.52/1.87  tff(v10_lattices, type, v10_lattices: $i > $o).
% 4.52/1.87  tff('#skF_9', type, '#skF_9': $i).
% 4.52/1.87  tff('#skF_8', type, '#skF_8': $i).
% 4.52/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.52/1.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.52/1.87  tff(v11_lattices, type, v11_lattices: $i > $o).
% 4.52/1.87  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.52/1.87  tff(v8_lattices, type, v8_lattices: $i > $o).
% 4.52/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.52/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.52/1.87  tff('#skF_6', type, '#skF_6': $i > $i).
% 4.52/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.52/1.87  tff(v7_lattices, type, v7_lattices: $i > $o).
% 4.52/1.87  
% 4.97/1.89  tff(f_185, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v11_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((k4_lattices(A, B, C) = k4_lattices(A, B, D)) & (k3_lattices(A, B, C) = k3_lattices(A, B, D))) => (C = D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_lattices)).
% 4.97/1.89  tff(f_51, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 4.97/1.89  tff(f_160, axiom, (![A]: (((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k1_lattices(A, B, B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_lattices)).
% 4.97/1.89  tff(f_97, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattices)).
% 4.97/1.89  tff(f_118, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 4.97/1.89  tff(f_144, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 4.97/1.89  tff(f_64, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k4_lattices(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 4.97/1.89  tff(f_112, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattices)).
% 4.97/1.89  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v11_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, C, D)) = k1_lattices(A, k2_lattices(A, B, C), k2_lattices(A, B, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_lattices)).
% 4.97/1.89  tff(f_131, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 4.97/1.89  tff(c_56, plain, ('#skF_11'!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.97/1.89  tff(c_62, plain, (m1_subset_1('#skF_11', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.97/1.89  tff(c_66, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.97/1.89  tff(c_74, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.97/1.89  tff(c_68, plain, (l3_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.97/1.89  tff(c_72, plain, (v10_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.97/1.89  tff(c_6, plain, (![A_3]: (v8_lattices(A_3) | ~v10_lattices(A_3) | v2_struct_0(A_3) | ~l3_lattices(A_3))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.97/1.89  tff(c_4, plain, (![A_3]: (v9_lattices(A_3) | ~v10_lattices(A_3) | v2_struct_0(A_3) | ~l3_lattices(A_3))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.97/1.89  tff(c_10, plain, (![A_3]: (v6_lattices(A_3) | ~v10_lattices(A_3) | v2_struct_0(A_3) | ~l3_lattices(A_3))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.97/1.89  tff(c_64, plain, (m1_subset_1('#skF_10', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.97/1.89  tff(c_113, plain, (![A_95, B_96]: (k1_lattices(A_95, B_96, B_96)=B_96 | ~m1_subset_1(B_96, u1_struct_0(A_95)) | ~l3_lattices(A_95) | ~v9_lattices(A_95) | ~v8_lattices(A_95) | ~v6_lattices(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.97/1.89  tff(c_129, plain, (k1_lattices('#skF_8', '#skF_10', '#skF_10')='#skF_10' | ~l3_lattices('#skF_8') | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_64, c_113])).
% 4.97/1.89  tff(c_143, plain, (k1_lattices('#skF_8', '#skF_10', '#skF_10')='#skF_10' | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_129])).
% 4.97/1.89  tff(c_144, plain, (k1_lattices('#skF_8', '#skF_10', '#skF_10')='#skF_10' | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_74, c_143])).
% 4.97/1.89  tff(c_153, plain, (~v6_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_144])).
% 4.97/1.89  tff(c_156, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_10, c_153])).
% 4.97/1.89  tff(c_159, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_156])).
% 4.97/1.89  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_159])).
% 4.97/1.89  tff(c_162, plain, (~v8_lattices('#skF_8') | ~v9_lattices('#skF_8') | k1_lattices('#skF_8', '#skF_10', '#skF_10')='#skF_10'), inference(splitRight, [status(thm)], [c_144])).
% 4.97/1.89  tff(c_164, plain, (~v9_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_162])).
% 4.97/1.89  tff(c_207, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_4, c_164])).
% 4.97/1.89  tff(c_210, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_207])).
% 4.97/1.89  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_210])).
% 4.97/1.89  tff(c_213, plain, (~v8_lattices('#skF_8') | k1_lattices('#skF_8', '#skF_10', '#skF_10')='#skF_10'), inference(splitRight, [status(thm)], [c_162])).
% 4.97/1.89  tff(c_215, plain, (~v8_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_213])).
% 4.97/1.89  tff(c_221, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_6, c_215])).
% 4.97/1.89  tff(c_224, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_221])).
% 4.97/1.89  tff(c_226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_224])).
% 4.97/1.89  tff(c_228, plain, (v8_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_213])).
% 4.97/1.89  tff(c_245, plain, (![A_100, B_101, C_102]: (k1_lattices(A_100, k2_lattices(A_100, B_101, C_102), C_102)=C_102 | ~m1_subset_1(C_102, u1_struct_0(A_100)) | ~m1_subset_1(B_101, u1_struct_0(A_100)) | ~v8_lattices(A_100) | ~l3_lattices(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.97/1.89  tff(c_261, plain, (![B_101]: (k1_lattices('#skF_8', k2_lattices('#skF_8', B_101, '#skF_10'), '#skF_10')='#skF_10' | ~m1_subset_1(B_101, u1_struct_0('#skF_8')) | ~v8_lattices('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_64, c_245])).
% 4.97/1.89  tff(c_275, plain, (![B_101]: (k1_lattices('#skF_8', k2_lattices('#skF_8', B_101, '#skF_10'), '#skF_10')='#skF_10' | ~m1_subset_1(B_101, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_228, c_261])).
% 4.97/1.89  tff(c_285, plain, (![B_103]: (k1_lattices('#skF_8', k2_lattices('#skF_8', B_103, '#skF_10'), '#skF_10')='#skF_10' | ~m1_subset_1(B_103, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_74, c_275])).
% 4.97/1.89  tff(c_353, plain, (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_10'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_66, c_285])).
% 4.97/1.89  tff(c_163, plain, (v6_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_144])).
% 4.97/1.89  tff(c_80, plain, (![A_77]: (l1_lattices(A_77) | ~l3_lattices(A_77))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.97/1.89  tff(c_84, plain, (l1_lattices('#skF_8')), inference(resolution, [status(thm)], [c_68, c_80])).
% 4.97/1.89  tff(c_516, plain, (![A_106, B_107, C_108]: (k4_lattices(A_106, B_107, C_108)=k2_lattices(A_106, B_107, C_108) | ~m1_subset_1(C_108, u1_struct_0(A_106)) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~l1_lattices(A_106) | ~v6_lattices(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.97/1.89  tff(c_536, plain, (![B_107]: (k4_lattices('#skF_8', B_107, '#skF_9')=k2_lattices('#skF_8', B_107, '#skF_9') | ~m1_subset_1(B_107, u1_struct_0('#skF_8')) | ~l1_lattices('#skF_8') | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_66, c_516])).
% 4.97/1.89  tff(c_554, plain, (![B_107]: (k4_lattices('#skF_8', B_107, '#skF_9')=k2_lattices('#skF_8', B_107, '#skF_9') | ~m1_subset_1(B_107, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_84, c_536])).
% 4.97/1.89  tff(c_654, plain, (![B_110]: (k4_lattices('#skF_8', B_110, '#skF_9')=k2_lattices('#skF_8', B_110, '#skF_9') | ~m1_subset_1(B_110, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_74, c_554])).
% 4.97/1.89  tff(c_720, plain, (k4_lattices('#skF_8', '#skF_10', '#skF_9')=k2_lattices('#skF_8', '#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_64, c_654])).
% 4.97/1.89  tff(c_532, plain, (![B_107]: (k4_lattices('#skF_8', B_107, '#skF_10')=k2_lattices('#skF_8', B_107, '#skF_10') | ~m1_subset_1(B_107, u1_struct_0('#skF_8')) | ~l1_lattices('#skF_8') | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_64, c_516])).
% 4.97/1.89  tff(c_546, plain, (![B_107]: (k4_lattices('#skF_8', B_107, '#skF_10')=k2_lattices('#skF_8', B_107, '#skF_10') | ~m1_subset_1(B_107, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_84, c_532])).
% 4.97/1.89  tff(c_568, plain, (![B_109]: (k4_lattices('#skF_8', B_109, '#skF_10')=k2_lattices('#skF_8', B_109, '#skF_10') | ~m1_subset_1(B_109, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_74, c_546])).
% 4.97/1.89  tff(c_636, plain, (k4_lattices('#skF_8', '#skF_9', '#skF_10')=k2_lattices('#skF_8', '#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_66, c_568])).
% 4.97/1.89  tff(c_1060, plain, (![A_120, C_121, B_122]: (k4_lattices(A_120, C_121, B_122)=k4_lattices(A_120, B_122, C_121) | ~m1_subset_1(C_121, u1_struct_0(A_120)) | ~m1_subset_1(B_122, u1_struct_0(A_120)) | ~l1_lattices(A_120) | ~v6_lattices(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.97/1.89  tff(c_1076, plain, (![B_122]: (k4_lattices('#skF_8', B_122, '#skF_10')=k4_lattices('#skF_8', '#skF_10', B_122) | ~m1_subset_1(B_122, u1_struct_0('#skF_8')) | ~l1_lattices('#skF_8') | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_64, c_1060])).
% 4.97/1.89  tff(c_1090, plain, (![B_122]: (k4_lattices('#skF_8', B_122, '#skF_10')=k4_lattices('#skF_8', '#skF_10', B_122) | ~m1_subset_1(B_122, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_84, c_1076])).
% 4.97/1.89  tff(c_1179, plain, (![B_124]: (k4_lattices('#skF_8', B_124, '#skF_10')=k4_lattices('#skF_8', '#skF_10', B_124) | ~m1_subset_1(B_124, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1090])).
% 4.97/1.89  tff(c_1216, plain, (k4_lattices('#skF_8', '#skF_10', '#skF_9')=k4_lattices('#skF_8', '#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_66, c_1179])).
% 4.97/1.89  tff(c_1250, plain, (k2_lattices('#skF_8', '#skF_10', '#skF_9')=k2_lattices('#skF_8', '#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_720, c_636, c_1216])).
% 4.97/1.89  tff(c_70, plain, (v11_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.97/1.89  tff(c_227, plain, (k1_lattices('#skF_8', '#skF_10', '#skF_10')='#skF_10'), inference(splitRight, [status(thm)], [c_213])).
% 4.97/1.89  tff(c_214, plain, (v9_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_162])).
% 4.97/1.89  tff(c_723, plain, (![A_111, B_112, C_113]: (k2_lattices(A_111, B_112, k1_lattices(A_111, B_112, C_113))=B_112 | ~m1_subset_1(C_113, u1_struct_0(A_111)) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~v9_lattices(A_111) | ~l3_lattices(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.97/1.89  tff(c_739, plain, (![B_112]: (k2_lattices('#skF_8', B_112, k1_lattices('#skF_8', B_112, '#skF_10'))=B_112 | ~m1_subset_1(B_112, u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_64, c_723])).
% 4.97/1.89  tff(c_753, plain, (![B_112]: (k2_lattices('#skF_8', B_112, k1_lattices('#skF_8', B_112, '#skF_10'))=B_112 | ~m1_subset_1(B_112, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_214, c_739])).
% 4.97/1.89  tff(c_862, plain, (![B_115]: (k2_lattices('#skF_8', B_115, k1_lattices('#skF_8', B_115, '#skF_10'))=B_115 | ~m1_subset_1(B_115, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_74, c_753])).
% 4.97/1.89  tff(c_885, plain, (k2_lattices('#skF_8', '#skF_10', k1_lattices('#skF_8', '#skF_10', '#skF_10'))='#skF_10'), inference(resolution, [status(thm)], [c_64, c_862])).
% 4.97/1.89  tff(c_919, plain, (k2_lattices('#skF_8', '#skF_10', '#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_227, c_885])).
% 4.97/1.89  tff(c_1446, plain, (![A_128, B_129, C_130, D_131]: (k1_lattices(A_128, k2_lattices(A_128, B_129, C_130), k2_lattices(A_128, B_129, D_131))=k2_lattices(A_128, B_129, k1_lattices(A_128, C_130, D_131)) | ~m1_subset_1(D_131, u1_struct_0(A_128)) | ~m1_subset_1(C_130, u1_struct_0(A_128)) | ~m1_subset_1(B_129, u1_struct_0(A_128)) | ~v11_lattices(A_128) | ~l3_lattices(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.97/1.89  tff(c_1528, plain, (![C_130]: (k2_lattices('#skF_8', '#skF_10', k1_lattices('#skF_8', C_130, '#skF_10'))=k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_10', C_130), '#skF_10') | ~m1_subset_1('#skF_10', u1_struct_0('#skF_8')) | ~m1_subset_1(C_130, u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_10', u1_struct_0('#skF_8')) | ~v11_lattices('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_919, c_1446])).
% 4.97/1.89  tff(c_1608, plain, (![C_130]: (k2_lattices('#skF_8', '#skF_10', k1_lattices('#skF_8', C_130, '#skF_10'))=k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_10', C_130), '#skF_10') | ~m1_subset_1(C_130, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_64, c_64, c_1528])).
% 4.97/1.89  tff(c_1955, plain, (![C_136]: (k2_lattices('#skF_8', '#skF_10', k1_lattices('#skF_8', C_136, '#skF_10'))=k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_10', C_136), '#skF_10') | ~m1_subset_1(C_136, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1608])).
% 4.97/1.89  tff(c_1992, plain, (k2_lattices('#skF_8', '#skF_10', k1_lattices('#skF_8', '#skF_9', '#skF_10'))=k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_10', '#skF_9'), '#skF_10')), inference(resolution, [status(thm)], [c_66, c_1955])).
% 4.97/1.89  tff(c_2026, plain, (k2_lattices('#skF_8', '#skF_10', k1_lattices('#skF_8', '#skF_9', '#skF_10'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_353, c_1250, c_1992])).
% 4.97/1.89  tff(c_14, plain, (![A_3]: (v4_lattices(A_3) | ~v10_lattices(A_3) | v2_struct_0(A_3) | ~l3_lattices(A_3))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.97/1.89  tff(c_75, plain, (![A_76]: (l2_lattices(A_76) | ~l3_lattices(A_76))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.97/1.89  tff(c_79, plain, (l2_lattices('#skF_8')), inference(resolution, [status(thm)], [c_68, c_75])).
% 4.97/1.89  tff(c_922, plain, (![A_116, B_117, C_118]: (k3_lattices(A_116, B_117, C_118)=k1_lattices(A_116, B_117, C_118) | ~m1_subset_1(C_118, u1_struct_0(A_116)) | ~m1_subset_1(B_117, u1_struct_0(A_116)) | ~l2_lattices(A_116) | ~v4_lattices(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.97/1.89  tff(c_942, plain, (![B_117]: (k3_lattices('#skF_8', B_117, '#skF_9')=k1_lattices('#skF_8', B_117, '#skF_9') | ~m1_subset_1(B_117, u1_struct_0('#skF_8')) | ~l2_lattices('#skF_8') | ~v4_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_66, c_922])).
% 4.97/1.89  tff(c_960, plain, (![B_117]: (k3_lattices('#skF_8', B_117, '#skF_9')=k1_lattices('#skF_8', B_117, '#skF_9') | ~m1_subset_1(B_117, u1_struct_0('#skF_8')) | ~v4_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_942])).
% 4.97/1.89  tff(c_961, plain, (![B_117]: (k3_lattices('#skF_8', B_117, '#skF_9')=k1_lattices('#skF_8', B_117, '#skF_9') | ~m1_subset_1(B_117, u1_struct_0('#skF_8')) | ~v4_lattices('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_74, c_960])).
% 4.97/1.89  tff(c_1435, plain, (~v4_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_961])).
% 4.97/1.89  tff(c_1438, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_14, c_1435])).
% 4.97/1.89  tff(c_1441, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_72, c_1438])).
% 4.97/1.89  tff(c_1443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1441])).
% 4.97/1.89  tff(c_1445, plain, (v4_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_961])).
% 4.97/1.89  tff(c_938, plain, (![B_117]: (k3_lattices('#skF_8', B_117, '#skF_10')=k1_lattices('#skF_8', B_117, '#skF_10') | ~m1_subset_1(B_117, u1_struct_0('#skF_8')) | ~l2_lattices('#skF_8') | ~v4_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_64, c_922])).
% 4.97/1.89  tff(c_952, plain, (![B_117]: (k3_lattices('#skF_8', B_117, '#skF_10')=k1_lattices('#skF_8', B_117, '#skF_10') | ~m1_subset_1(B_117, u1_struct_0('#skF_8')) | ~v4_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_938])).
% 4.97/1.89  tff(c_953, plain, (![B_117]: (k3_lattices('#skF_8', B_117, '#skF_10')=k1_lattices('#skF_8', B_117, '#skF_10') | ~m1_subset_1(B_117, u1_struct_0('#skF_8')) | ~v4_lattices('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_74, c_952])).
% 4.97/1.89  tff(c_1700, plain, (![B_133]: (k3_lattices('#skF_8', B_133, '#skF_10')=k1_lattices('#skF_8', B_133, '#skF_10') | ~m1_subset_1(B_133, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_1445, c_953])).
% 4.97/1.89  tff(c_1769, plain, (k3_lattices('#skF_8', '#skF_9', '#skF_10')=k1_lattices('#skF_8', '#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_66, c_1700])).
% 4.97/1.89  tff(c_58, plain, (k3_lattices('#skF_8', '#skF_9', '#skF_11')=k3_lattices('#skF_8', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.97/1.89  tff(c_1774, plain, (k3_lattices('#skF_8', '#skF_9', '#skF_11')=k1_lattices('#skF_8', '#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1769, c_58])).
% 4.97/1.89  tff(c_940, plain, (![B_117]: (k3_lattices('#skF_8', B_117, '#skF_11')=k1_lattices('#skF_8', B_117, '#skF_11') | ~m1_subset_1(B_117, u1_struct_0('#skF_8')) | ~l2_lattices('#skF_8') | ~v4_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_62, c_922])).
% 4.97/1.89  tff(c_956, plain, (![B_117]: (k3_lattices('#skF_8', B_117, '#skF_11')=k1_lattices('#skF_8', B_117, '#skF_11') | ~m1_subset_1(B_117, u1_struct_0('#skF_8')) | ~v4_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_940])).
% 4.97/1.89  tff(c_957, plain, (![B_117]: (k3_lattices('#skF_8', B_117, '#skF_11')=k1_lattices('#skF_8', B_117, '#skF_11') | ~m1_subset_1(B_117, u1_struct_0('#skF_8')) | ~v4_lattices('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_74, c_956])).
% 4.97/1.89  tff(c_1785, plain, (![B_134]: (k3_lattices('#skF_8', B_134, '#skF_11')=k1_lattices('#skF_8', B_134, '#skF_11') | ~m1_subset_1(B_134, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_1445, c_957])).
% 4.97/1.89  tff(c_1854, plain, (k3_lattices('#skF_8', '#skF_9', '#skF_11')=k1_lattices('#skF_8', '#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_66, c_1785])).
% 4.97/1.89  tff(c_1863, plain, (k1_lattices('#skF_8', '#skF_9', '#skF_11')=k1_lattices('#skF_8', '#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1774, c_1854])).
% 4.97/1.89  tff(c_1465, plain, (![D_131]: (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_10'), k2_lattices('#skF_8', '#skF_10', D_131))=k2_lattices('#skF_8', '#skF_10', k1_lattices('#skF_8', '#skF_9', D_131)) | ~m1_subset_1(D_131, u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_10', u1_struct_0('#skF_8')) | ~v11_lattices('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1250, c_1446])).
% 4.97/1.89  tff(c_1545, plain, (![D_131]: (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_10'), k2_lattices('#skF_8', '#skF_10', D_131))=k2_lattices('#skF_8', '#skF_10', k1_lattices('#skF_8', '#skF_9', D_131)) | ~m1_subset_1(D_131, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_64, c_66, c_1465])).
% 4.97/1.89  tff(c_3065, plain, (![D_161]: (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_10'), k2_lattices('#skF_8', '#skF_10', D_161))=k2_lattices('#skF_8', '#skF_10', k1_lattices('#skF_8', '#skF_9', D_161)) | ~m1_subset_1(D_161, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1545])).
% 4.97/1.89  tff(c_60, plain, (k4_lattices('#skF_8', '#skF_9', '#skF_11')=k4_lattices('#skF_8', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_185])).
% 4.97/1.89  tff(c_645, plain, (k4_lattices('#skF_8', '#skF_9', '#skF_11')=k2_lattices('#skF_8', '#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_636, c_60])).
% 4.97/1.89  tff(c_534, plain, (![B_107]: (k4_lattices('#skF_8', B_107, '#skF_11')=k2_lattices('#skF_8', B_107, '#skF_11') | ~m1_subset_1(B_107, u1_struct_0('#skF_8')) | ~l1_lattices('#skF_8') | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_62, c_516])).
% 4.97/1.89  tff(c_550, plain, (![B_107]: (k4_lattices('#skF_8', B_107, '#skF_11')=k2_lattices('#skF_8', B_107, '#skF_11') | ~m1_subset_1(B_107, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_84, c_534])).
% 4.97/1.89  tff(c_775, plain, (![B_114]: (k4_lattices('#skF_8', B_114, '#skF_11')=k2_lattices('#skF_8', B_114, '#skF_11') | ~m1_subset_1(B_114, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_74, c_550])).
% 4.97/1.89  tff(c_812, plain, (k4_lattices('#skF_8', '#skF_9', '#skF_11')=k2_lattices('#skF_8', '#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_66, c_775])).
% 4.97/1.89  tff(c_844, plain, (k2_lattices('#skF_8', '#skF_9', '#skF_11')=k2_lattices('#skF_8', '#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_645, c_812])).
% 4.97/1.89  tff(c_263, plain, (![B_101]: (k1_lattices('#skF_8', k2_lattices('#skF_8', B_101, '#skF_11'), '#skF_11')='#skF_11' | ~m1_subset_1(B_101, u1_struct_0('#skF_8')) | ~v8_lattices('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_62, c_245])).
% 4.97/1.89  tff(c_279, plain, (![B_101]: (k1_lattices('#skF_8', k2_lattices('#skF_8', B_101, '#skF_11'), '#skF_11')='#skF_11' | ~m1_subset_1(B_101, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_228, c_263])).
% 4.97/1.89  tff(c_366, plain, (![B_104]: (k1_lattices('#skF_8', k2_lattices('#skF_8', B_104, '#skF_11'), '#skF_11')='#skF_11' | ~m1_subset_1(B_104, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_74, c_279])).
% 4.97/1.89  tff(c_434, plain, (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_11'), '#skF_11')='#skF_11'), inference(resolution, [status(thm)], [c_66, c_366])).
% 4.97/1.89  tff(c_853, plain, (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_10'), '#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_844, c_434])).
% 4.97/1.89  tff(c_721, plain, (k4_lattices('#skF_8', '#skF_11', '#skF_9')=k2_lattices('#skF_8', '#skF_11', '#skF_9')), inference(resolution, [status(thm)], [c_62, c_654])).
% 4.97/1.89  tff(c_1080, plain, (![B_122]: (k4_lattices('#skF_8', B_122, '#skF_9')=k4_lattices('#skF_8', '#skF_9', B_122) | ~m1_subset_1(B_122, u1_struct_0('#skF_8')) | ~l1_lattices('#skF_8') | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_66, c_1060])).
% 4.97/1.89  tff(c_1098, plain, (![B_122]: (k4_lattices('#skF_8', B_122, '#skF_9')=k4_lattices('#skF_8', '#skF_9', B_122) | ~m1_subset_1(B_122, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_84, c_1080])).
% 4.97/1.89  tff(c_1280, plain, (![B_126]: (k4_lattices('#skF_8', B_126, '#skF_9')=k4_lattices('#skF_8', '#skF_9', B_126) | ~m1_subset_1(B_126, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1098])).
% 4.97/1.89  tff(c_1314, plain, (k4_lattices('#skF_8', '#skF_11', '#skF_9')=k4_lattices('#skF_8', '#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_62, c_1280])).
% 4.97/1.89  tff(c_1349, plain, (k2_lattices('#skF_8', '#skF_11', '#skF_9')=k2_lattices('#skF_8', '#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_721, c_645, c_1314])).
% 4.97/1.89  tff(c_131, plain, (k1_lattices('#skF_8', '#skF_11', '#skF_11')='#skF_11' | ~l3_lattices('#skF_8') | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_62, c_113])).
% 4.97/1.89  tff(c_147, plain, (k1_lattices('#skF_8', '#skF_11', '#skF_11')='#skF_11' | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_131])).
% 4.97/1.89  tff(c_148, plain, (k1_lattices('#skF_8', '#skF_11', '#skF_11')='#skF_11' | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~v6_lattices('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_74, c_147])).
% 4.97/1.89  tff(c_240, plain, (k1_lattices('#skF_8', '#skF_11', '#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_228, c_214, c_148])).
% 4.97/1.89  tff(c_741, plain, (![B_112]: (k2_lattices('#skF_8', B_112, k1_lattices('#skF_8', B_112, '#skF_11'))=B_112 | ~m1_subset_1(B_112, u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_62, c_723])).
% 4.97/1.89  tff(c_757, plain, (![B_112]: (k2_lattices('#skF_8', B_112, k1_lattices('#skF_8', B_112, '#skF_11'))=B_112 | ~m1_subset_1(B_112, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_214, c_741])).
% 4.97/1.89  tff(c_981, plain, (![B_119]: (k2_lattices('#skF_8', B_119, k1_lattices('#skF_8', B_119, '#skF_11'))=B_119 | ~m1_subset_1(B_119, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_74, c_757])).
% 4.97/1.89  tff(c_1006, plain, (k2_lattices('#skF_8', '#skF_11', k1_lattices('#skF_8', '#skF_11', '#skF_11'))='#skF_11'), inference(resolution, [status(thm)], [c_62, c_981])).
% 4.97/1.89  tff(c_1039, plain, (k2_lattices('#skF_8', '#skF_11', '#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_240, c_1006])).
% 4.97/1.89  tff(c_1510, plain, (![C_130]: (k2_lattices('#skF_8', '#skF_11', k1_lattices('#skF_8', C_130, '#skF_11'))=k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_11', C_130), '#skF_11') | ~m1_subset_1('#skF_11', u1_struct_0('#skF_8')) | ~m1_subset_1(C_130, u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_8')) | ~v11_lattices('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1039, c_1446])).
% 4.97/1.89  tff(c_1590, plain, (![C_130]: (k2_lattices('#skF_8', '#skF_11', k1_lattices('#skF_8', C_130, '#skF_11'))=k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_11', C_130), '#skF_11') | ~m1_subset_1(C_130, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_62, c_62, c_1510])).
% 4.97/1.89  tff(c_2341, plain, (![C_142]: (k2_lattices('#skF_8', '#skF_11', k1_lattices('#skF_8', C_142, '#skF_11'))=k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_11', C_142), '#skF_11') | ~m1_subset_1(C_142, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1590])).
% 4.97/1.89  tff(c_2378, plain, (k2_lattices('#skF_8', '#skF_11', k1_lattices('#skF_8', '#skF_9', '#skF_11'))=k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_11', '#skF_9'), '#skF_11')), inference(resolution, [status(thm)], [c_66, c_2341])).
% 4.97/1.89  tff(c_2412, plain, (k2_lattices('#skF_8', '#skF_11', k1_lattices('#skF_8', '#skF_9', '#skF_10'))='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_853, c_1349, c_2378])).
% 4.97/1.89  tff(c_841, plain, (k4_lattices('#skF_8', '#skF_10', '#skF_11')=k2_lattices('#skF_8', '#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_64, c_775])).
% 4.97/1.89  tff(c_635, plain, (k4_lattices('#skF_8', '#skF_11', '#skF_10')=k2_lattices('#skF_8', '#skF_11', '#skF_10')), inference(resolution, [status(thm)], [c_62, c_568])).
% 4.97/1.89  tff(c_1213, plain, (k4_lattices('#skF_8', '#skF_11', '#skF_10')=k4_lattices('#skF_8', '#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_62, c_1179])).
% 4.97/1.89  tff(c_1248, plain, (k2_lattices('#skF_8', '#skF_11', '#skF_10')=k2_lattices('#skF_8', '#skF_10', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_841, c_635, c_1213])).
% 4.97/1.89  tff(c_1474, plain, (![C_130]: (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_11', C_130), k2_lattices('#skF_8', '#skF_10', '#skF_11'))=k2_lattices('#skF_8', '#skF_11', k1_lattices('#skF_8', C_130, '#skF_10')) | ~m1_subset_1('#skF_10', u1_struct_0('#skF_8')) | ~m1_subset_1(C_130, u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_8')) | ~v11_lattices('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1248, c_1446])).
% 4.97/1.89  tff(c_1554, plain, (![C_130]: (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_11', C_130), k2_lattices('#skF_8', '#skF_10', '#skF_11'))=k2_lattices('#skF_8', '#skF_11', k1_lattices('#skF_8', C_130, '#skF_10')) | ~m1_subset_1(C_130, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_62, c_64, c_1474])).
% 4.97/1.89  tff(c_2413, plain, (![C_143]: (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_11', C_143), k2_lattices('#skF_8', '#skF_10', '#skF_11'))=k2_lattices('#skF_8', '#skF_11', k1_lattices('#skF_8', C_143, '#skF_10')) | ~m1_subset_1(C_143, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1554])).
% 4.97/1.89  tff(c_2422, plain, (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_10'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))=k2_lattices('#skF_8', '#skF_11', k1_lattices('#skF_8', '#skF_9', '#skF_10')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1349, c_2413])).
% 4.97/1.89  tff(c_2438, plain, (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_10'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))=k2_lattices('#skF_8', '#skF_11', k1_lattices('#skF_8', '#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2422])).
% 4.97/1.89  tff(c_2501, plain, (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_10'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_2412, c_2438])).
% 4.97/1.89  tff(c_3071, plain, (k2_lattices('#skF_8', '#skF_10', k1_lattices('#skF_8', '#skF_9', '#skF_11'))='#skF_11' | ~m1_subset_1('#skF_11', u1_struct_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3065, c_2501])).
% 4.97/1.89  tff(c_3118, plain, ('#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2026, c_1863, c_3071])).
% 4.97/1.89  tff(c_3120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_3118])).
% 4.97/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.97/1.89  
% 4.97/1.89  Inference rules
% 4.97/1.89  ----------------------
% 4.97/1.89  #Ref     : 1
% 4.97/1.89  #Sup     : 608
% 4.97/1.89  #Fact    : 0
% 4.97/1.89  #Define  : 0
% 4.97/1.89  #Split   : 10
% 4.97/1.89  #Chain   : 0
% 4.97/1.89  #Close   : 0
% 4.97/1.89  
% 4.97/1.89  Ordering : KBO
% 4.97/1.89  
% 4.97/1.89  Simplification rules
% 4.97/1.89  ----------------------
% 4.97/1.89  #Subsume      : 17
% 4.97/1.89  #Demod        : 795
% 4.97/1.89  #Tautology    : 406
% 4.97/1.89  #SimpNegUnit  : 250
% 4.97/1.89  #BackRed      : 18
% 4.97/1.89  
% 4.97/1.89  #Partial instantiations: 0
% 4.97/1.89  #Strategies tried      : 1
% 4.97/1.89  
% 4.97/1.89  Timing (in seconds)
% 4.97/1.89  ----------------------
% 4.97/1.90  Preprocessing        : 0.36
% 4.97/1.90  Parsing              : 0.19
% 4.97/1.90  CNF conversion       : 0.03
% 4.97/1.90  Main loop            : 0.77
% 4.97/1.90  Inferencing          : 0.26
% 4.97/1.90  Reduction            : 0.28
% 4.97/1.90  Demodulation         : 0.20
% 4.97/1.90  BG Simplification    : 0.04
% 4.97/1.90  Subsumption          : 0.14
% 4.97/1.90  Abstraction          : 0.04
% 4.97/1.90  MUC search           : 0.00
% 4.97/1.90  Cooper               : 0.00
% 4.97/1.90  Total                : 1.19
% 4.97/1.90  Index Insertion      : 0.00
% 4.97/1.90  Index Deletion       : 0.00
% 4.97/1.90  Index Matching       : 0.00
% 4.97/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
